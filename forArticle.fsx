let histogram lst =
    List.fold
        (fun acc key ->
            if Map.containsKey key acc then
                Map.add key (acc.[key] + 1) acc
            else
                Map.add key 1 acc)
        Map.empty
        lst

let mapKeys mp =
    Map.fold (fun acc k _ -> Set.add k acc) Set.empty mp

let keysUnion a b = Set.union (a |> mapKeys) (b |> mapKeys)

let getAnyKey (m : Map<'a,'b>) =
    let p = m |> Seq.head in p.Key

let getValue key (map: Map<'a, 'b>) =
    Option.defaultValue Unchecked.defaultof<'b> (Map.tryFind key map)

let subtractHistograms a b =
    let keys = keysUnion a b

    Set.fold (fun acc k ->
              Map.add k ((getValue k a) - (getValue k b)) acc) Map.empty keys
    |> Map.filter (fun k v -> v <> 0)

let rec sieve windowSz (currH : Map<'a,'b>) tgH candidates =
    List.foldBack
        (fun (signal : int list) (acc : int list list)->
            let langis = List.rev signal.[0..windowSz-1]

            match langis with
            | [] -> acc
            | v :: tsr ->
                let currH' = Map.add v (currH.[v] - 1) currH
                let hDiff = subtractHistograms tgH currH'
                if hDiff.Count > 1 then
                    acc
                else
                    let newV = getAnyKey hDiff
                    (newV :: signal)::acc
        )
        candidates
        []

/// Adapted from https://stackoverflow.com/questions/1526046/f-permutations
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

let solve windowSz histLst =
    let rec next histTsl candidates =
        match histTsl with
        [] | [_] -> candidates
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

let signal = [0; 1; 0; 1; 1]
let windowSize = 3;
let histogramList =
    signal
    |> List.windowed windowSize
    |> List.map histogram
let solutions = solve windowSize histogramList
printfn "%A" solutions