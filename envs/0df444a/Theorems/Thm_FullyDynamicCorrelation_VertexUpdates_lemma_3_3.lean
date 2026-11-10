-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_3_3
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:54:47.502454+00:00
-- url     : https://prove2.me/theorems/3f05ab67-da9f-4850-80e2-d0b5899feb8b
-- title:
--   Lemma 3.3 — identifying the outside vertices adjacent to a fraction of an almost-clique
-- statement:
--   For every $c>0$ there is $C>0$ such that for all $0<\gamma\le\delta/2<1$ and $\varepsilon\le1/2$ there is a program with the following property. For every $\varepsilon$-almost-clique $C$ (given as a list without repetition) of a graph with vertex names $<n$, $n\ge2$, the program always halts within $\lfloor C|C|\log_2n/\delta\rfloor$ instructions, and with probability at least $1-n^{-c}$ its output list $\bar C$ satisfies $\bar C\subseteq V\setminus C$, contains every $u\in V\setminus C$ with $|N(u)\cap C|\ge\delta|C|$, and contains no vertex with $|N(u)\cap C|\le\gamma|C|$.
--
--   Differences from the source:
--   - encoding: an algorithm in the adjacency-list model with O(1)-time queries → a Program of the unit-cost RAM (RAM module): constants, +, truncated −, indirect access, jumps, degree / neighbour / edge queries and uniform random choice, one unit per executed instruction; reason: fixes the paper’s operation count; with no multiplication or division the machine is no stronger than the paper’s
--   - encoding: the graph G and its adjacency list → an SGraph whose vertex names are < n, presented by adjacency lists adj in arbitrary order (Presents); reason: the lists are given to the algorithm; their order is not under its control
--   - reading: “with high probability” → for every c > 0 there are constants and a program with failure probability at most n^(−c), for every n ≥ 2; reason: the standard meaning, made explicit by the amplification remark of p. 18 (log n → log(n/ξ))
--   - encoding: “an ε-almost-clique C” → a list xs without repetition whose set is an ε-almost-clique, stored as the input list; reason: input convention
--   - encoding: “runs in O(|C| log n/δ) time” (a separate sentence, outside “with high probability”) → every outcome of the run with that allowance halts (no allowance exhaustion in the support); reason: the time bound is stated unconditionally
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 3.3, p. 17

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_RAM

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 3.3 (p. 17). -/
theorem lemma_3_3 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ γ δ ε : ℝ, 0 < γ → γ ≤ δ / 2 → δ / 2 < 1 → ε ≤ 1 / 2 →
        ∃ P : Program,
          ∀ n : ℕ, 2 ≤ n → ∀ H : SGraph, (∀ v ∈ H.V, v < n) →
            ∀ adj : ℕ → List ℕ, Presents H adj →
              ∀ xs : List ℕ, xs.Nodup → H.IsAlmostClique ε xs.toFinset →
                (∀ o ∈ (runCall P H adj (inputMem n 0 xs (fun _ => 0) (fun _ => 0))
                    ⌊C * (xs.length : ℝ) * lg n / δ⌋₊).support, o.isSome) ∧
                1 - (n : ℝ) ^ (-c) ≤
                  ((runCall P H adj (inputMem n 0 xs (fun _ => 0) (fun _ => 0))
                      ⌊C * (xs.length : ℝ) * lg n / δ⌋₊).toOuterMeasure
                    {o | ∃ (m : ℕ → ℕ) (st : ℕ), o = some (m, st) ∧
                      (∀ u ∈ outputList m, u ∈ H.V \ xs.toFinset) ∧
                      (∀ u ∈ H.V \ xs.toFinset,
                        δ * (xs.length : ℝ) ≤ (((H.nbr u ∩ xs.toFinset).card : ℕ) : ℝ) →
                          u ∈ outputList m) ∧
                      (∀ u ∈ outputList m,
                        γ * (xs.length : ℝ) < (((H.nbr u ∩ xs.toFinset).card : ℕ) : ℝ))}).toReal := by sorry

end FullyDynamicCorrelation.VertexUpdates
