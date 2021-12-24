type Histogram<'a when 'a: comparison> = Map<'a, int>

/// <summary> Generate a (sparse) histogram </summary>
/// <param name="lst">The list of signal values</param>
/// <typeparam name="'a">Any value with has the comparison operator defined</typeparam>
/// <returns>A map of signal values and their occurrence counts in lst</returns>
let histogram<'a when 'a: comparison> (lst: 'a list) : Histogram<'a> =
    List.fold
        (fun acc key ->
            if Map.containsKey key acc then
                Map.add key (acc.[key] + 1) acc
            else
                Map.add key 1 acc)
        Map.empty
        lst

/// Return the set of (unique) keys in a map (Map.keys is not defined in mono)
let mapKeys (mp: Map<'a, 'b>) =
    Map.fold (fun acc k _ -> Set.add k acc) Set.empty mp

/// Return the set-union of keys from two maps
let keysUnion (a: Histogram<'a>) (b: Histogram<'a>) = Set.union (a |> mapKeys) (b |> mapKeys)

/// Return the value of a map with default value if non-existent. Warning, unsafe since some values do not have proper null values.
let getValue key (map: Map<'a, 'b>) =
    Option.defaultValue Unchecked.defaultof<'b> (Map.tryFind key map)

/// Get any key from a map. This probably goes wrong, if the map is empty....
let getAnyKey (m: Map<'a, 'b>) = let p = m |> Seq.head in p.Key

/// Subtract 2 histograms and return the sparse result (all zero-counts removed)
let subtractHistograms<'a when 'a: comparison> (a: Histogram<'a>) (b: Histogram<'a>) : Histogram<'a> =
    let keys = keysUnion a b

    Set.fold (fun acc k -> Map.add k ((getValue k a) - (getValue k b)) acc) Map.empty keys // Subtract sparse histograms
    |> Map.filter (fun k v -> v <> 0) // Remove all histogram bins with zero counts.

/// Pick every n'th element from a list. Adapted from https://stackoverflow.com/questions/4676529/getting-every-nth-element-of-a-sequence
let everyNth (n: int) (elm: 'a list) =
    elm
    |> List.mapi (fun i e -> if i % n = 0 then Some(e) else None)
    |> List.choose id

let isEqual (lst: 'a list when 'a: comparison) =
    List.fold (fun acc elm -> acc && (elm = lst.[0])) true lst

let isPeriodic (n: int) (lst: 'a list) =
    List.map (fun i -> (everyNth n lst.[i..] |> isEqual)) [ 0 .. n - 1 ]
    |> List.reduce (||)

// convert an integer n to a list of integers representing the digits in its representation on base b
let int2Base b n =
    let rec int2BaseRest b n lst =
        if n < b then
            n :: lst
        else
            int2BaseRest b (n / b) (n % b :: lst)

    int2BaseRest b n []

// convert the digits of a base b into an integer
let rec base2Int b lst =
    let rec base2IntRest b lst p =
        match lst with
        | d :: rst -> p * d + base2IntRest b rst (b * p)
        | _ -> 0

    base2IntRest b (List.rev lst) 1

// return a signal with index from an enumeration of all signals of length signalSize and from an alphabet of [0..alphabetSize]
let enumeratedSignals (alphabetSize: int) (signalSize: int) (s: int) : int list =
    let tmp = int2Base alphabetSize s

    (if tmp.Length < signalSize then
         List.replicate (signalSize - tmp.Length) 0
     else
         [])
    @ tmp

let rnd = System.Random()

// return a random signal of length signalSize and from an alphabet of [0..alphabetSize]. Index s is ignored.
let randomSignal (alphabetSize: int) (signalSize: int) (s: int) : int list =
    List.init signalSize (fun e -> rnd.Next alphabetSize)

/// all permutations of a list, adapted from https://stackoverflow.com/questions/1526046/f-permutations
let rec permute l =
    let rec distribute e l =
        match l with
        | [] -> [ [ e ] ]
        | x :: xs' as xs ->
            (e :: xs)
            :: [ for xs in distribute e xs' -> x :: xs ]

    match l with
    | [] -> [ [] ]
    | e :: xs -> List.collect (distribute e) (permute xs)

/// Consider all present candidate signals whose last windowed histogram is currH, and return a new list of signal candidates which is one element longer, and which now has gH as its last windowed histogram.
let rec sieve (windowSz: int) (currH :Histogram<'a>) (tgH: Histogram<'a>) (candidates: int list list) =
    // lst contains all current candidates of reconstructions up to length n, histLst contains histogram for current head of and all remaining histograms, second element being the next to consider
    List.foldBack
        (fun (signal : int list) (acc : int list list)->
            let langis = List.rev signal.[0..windowSz-1] // we reverse since we need to remove the last element

            match langis with
            | [] -> acc // This would be weird since all candidates must be longer than windowsize
            | v :: tsr ->
                let currH' = Map.add v (currH.[v] - 1) currH // remove the contribution of v histogram
                let hDiff = subtractHistograms tgH currH'
                if hDiff.Count > 1 then // there can be only one
                    acc
                else
                    let newV = getAnyKey hDiff
                    (newV :: signal)::acc
        )
        candidates
        []

/// <summary> Solve for a signal given its set of local and overlapping histograms </summary>
/// <param name="windowSz"> The window size used to calculate the histograms </param>
/// <param name="histLst"> The list of histograms </param>
/// <returns>A reconstructed signal as an option list. None is used if a value is undecidable </returns>
let solve (windowSz: int) (histLst: Histogram<'a> list) =
    let rec next (histTsl: Histogram<'a> list) (candidates : int list list) =
        // s contains all the possible solutions till now.
        // histTsl is a list of histograms where the first was used to solve for s at the present state.
        match histTsl with
        [] | [_] -> candidates // if histTsl is empty or contains only one element, then we are done.
        |  currH :: tgH :: histRst ->
            let newCandidates = sieve windowSz currH tgH candidates
            next (tgH::histRst) newCandidates

    let histTsl = List.rev histLst
    match histTsl with
    | [] -> [[]]
    | h::_ ->
        h
        |> Map.fold (fun acc k v -> (List.replicate v k) @ acc) []
        |> permute
        |> List.distinct
        |> next histTsl

/// Count the number of signals that could not uniquely be determined. Signals are drawn from getSignal with index from range, sliding histograms of windows with size windowSize are computed, and signals is reconstructed from these histograms, when possible.
let experiment1 (getSignal: int -> int list) (range: int list) (windowSize: int) (debug: int) : int * Set<int list list> =
    let mutable count = 0
    let mutable m = Set.empty

    for s in range do
        let signal = getSignal s
        if debug > 0 then printfn "%A" signal

        let slidingWins = List.windowed windowSize signal

        if debug > 0 then
            printfn "The list of sliding histograms"

        let slidingWinsHists = List.map histogram slidingWins

        if debug > 0 then
            printfn "%A" slidingWinsHists

        if debug > 0 then
            let periodic = isPeriodic windowSize signal
            printfn "The signal is %squasi-periodic." (if periodic then "" else "not ")

        let solutions =
            solve windowSize slidingWinsHists
        let foundSolution = solutions.Length = 1
        
        if debug > 0 then
            printfn "%b solution found" foundSolution

        if foundSolution then
            count <- count + 1
        else
            let k = (List.sort solutions)
            m <- Set.add k m
    (count,m)

/// Swap the order of arguments
let swap f a b = f b a

/// Calculate the array of metameric signals which have the same list of sliding histogram.
let experiment2 (alphabetSize: int) (signalSize: int) (windowSize: int) (debug: int) : int * Set<int list list>  =
    let getSignal =
        enumeratedSignals alphabetSize signalSize

    let n = pown alphabetSize signalSize
    let metamerics = Array.replicate<int list> n []

    let generateHistograms i =
        i
        |> getSignal
        |> List.windowed windowSize
        |> List.map histogram

    let allHistograms =
        List.foldBack (fun i acc -> (generateHistograms i) :: acc) [ 0 .. n - 1 ] []

    let allSignals =
        List.foldBack (fun i acc -> (getSignal i) :: acc) [ 0 .. n - 1 ] []

    if debug > 2 then
        List.iteri (fun i e -> printfn "%d: %A" i e) (List.zip allSignals allHistograms)

    for i = 0 to (n - 1) do
        for j = (i + 1) to (n - 1) do
            //            printfn "%d vs %d" i j
            if List.forall2 (=) allHistograms.[i] allHistograms.[j] then
                metamerics.[i] <- j :: metamerics.[i]
                metamerics.[j] <- i :: metamerics.[j]

    if debug > 2 then
        Array.iteri
            (fun (i: int) (e: int list) ->
                if e.Length > 0 then
                    printfn "%d: %A\n %A\n %4d: %A" i e allHistograms.[i] i allSignals.[i]
                    List.iter (fun (j: int) -> printfn " %4d: %A" j allSignals.[j]) e)
            metamerics
    let mutable m = Set.empty
    Array.iteri (fun i (e : int list) -> if not (List.isEmpty e) then m <- i::e |> List.map getSignal |> List.sort |> swap Set.add m) metamerics    
    //printfn "\n%A\n%A\n" m metamerics
    let count = Array.fold (fun acc e -> acc + if List.isEmpty e then 1 else 0) 0 metamerics
    (count, m)

let experiment3 (signalSize: int) (debug: int) =
    let alphabetSize = 2
    let windowSize = signalSize - 1
    let getSignal =
        enumeratedSignals alphabetSize signalSize

    let n = pown alphabetSize signalSize
    let arr = Array2D.create (windowSize+1) (windowSize+1) []

    let generateHistograms i =
        i
        |> getSignal
        |> List.windowed windowSize
        |> List.map histogram

    let allHistograms =
        List.foldBack (fun i acc -> (generateHistograms i) :: acc) [ 0 .. n - 1 ] []

    let allSignals =
        List.foldBack (fun i acc -> (getSignal i) :: acc) [ 0 .. n - 1 ] []

    List.iter2 (fun s (h : Histogram<int> list) -> 
            let i = getValue 1 h.[0]
            let j = getValue 1 h.[1]
            arr.[i,j] <- s::arr.[i,j]
            ) allSignals allHistograms
    Array2D.map List.sort arr 

[<EntryPoint>]
let main argv =
    let exp = 4
    let debug = 0

    match exp with
    | 1 | 2->

        printfn "alphabetSize, signalSize, windowSizes, # signals, # unique solutions, # metameric classes"
        for alphabetSize in [2 .. 3] do
            for signalSize in [2 .. 6] do
                for windowSize in [2 .. signalSize] do
                    printf "%4d, %4d, %4d, %4d" alphabetSize signalSize windowSize (pown alphabetSize signalSize)
                    // Signal functions: randomSignal, enumerated Signals
                    let getSignal =
                        enumeratedSignals alphabetSize signalSize

                    let range =
                        [ 0 .. pown alphabetSize signalSize - 1 ]

                    let count, m =
                        match exp with
                        1 ->
                            experiment1 getSignal range windowSize debug
                        | 2 ->
                            experiment2 alphabetSize signalSize windowSize debug
                    printfn ", %4d, %4d" count m.Count
                    if debug>0 then if m.Count < 9 then Set.iter (printfn "%A") m
    | 3 ->
        for signalSize = 3 to 6 do
            let confTbl = experiment3 signalSize debug
            printfn "%d:\n%A" signalSize confTbl
    | 4 ->
        let alphabetSize = 2
        let signalSize = 10
        let windowSize = 3;
        printf "%4d, %4d, %4d, %4d" alphabetSize signalSize windowSize (pown alphabetSize signalSize)
        // Signal functions: randomSignal, enumerated Signals
        let getSignal =
            enumeratedSignals alphabetSize signalSize

        let range =
            [ 0 .. pown alphabetSize signalSize - 1 ]

        let count, m = experiment1 getSignal range windowSize debug
        printfn ", %4d, %4d" count m.Count
        if debug>0 then if m.Count < 9 then Set.iter (printfn "%A") m

    | _ -> printfn "Unknown experiment"

    0
