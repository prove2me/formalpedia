-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_17_5
-- name    : MinDegST.AddOne.lemma_17_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:01.158119+00:00
-- url     : https://prove2.me/theorems/54448cba-5831-4d54-bd02-80f1c932f910
-- title:
--   Lemma 17.5 — a greedy independent set of size ≥ n²/(n + 2m) in O(n + m) time
-- statement:
--   There are one deterministic word-RAM program and a constant $K>0$ such that for every simple graph $G$ with $n\ge1$ nodes and $m$ edges, given by adjacency lists (each list in any order), the program halts within
--   $$K\cdot(n+m)+K$$
--   steps and outputs an independent set $I$ of $G$ with
--   $$|I|\ \ge\ \frac{n^2}{n+2m}.$$
--   Cited from [Hoc97] (the Turán-type bound $n^2/(n+2m)\ge n/(\bar d+1)$); it extracts the parallel set from the sparse conflict graph in Lemma 17.2.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: O(n + m) time → ∃ K > 0: cost ≤ K·(n + m) + K; reason: explicit constant
--   - encoding: G given by adjacency lists; find an independent set I ⊆ V → input [n, m, deg(0), N(0), …, deg(n−1), N(n−1)] with each list in any order; output the nodes of I, each once; reason: a concrete input/output layout for the RAM
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 49, Lemma 17.5

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine

namespace MinDegST.AddOne

/-- **Lemma 17.5** ([Hoc97]). One deterministic word-RAM program and a constant `K > 0` such that:
for every simple graph `G` on `Fin n` with `n ≥ 1` and `m` edges, given by adjacency lists `adj`
(each list in any order), the program halts within `K · (n + m) + K` steps and outputs the nodes of
an independent set `I` of `G` with `|I| ≥ n² / (n + 2m)`. -/
theorem lemma_17_5 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (adj : Fin n → List (Fin n)),
        1 ≤ n → IsAdjListsOf G adj →
          WordBounded P (encAdj n (numEdges G) adj) width (n + numEdges G) ∧
          HaltsWithin P (encAdj n (numEdges G) adj) (K * ((n : ℝ) + numEdges G) + K)
            (fun out => ∃ I : Finset (Fin n), EncodesSet out I ∧
              (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
              (n : ℝ) ^ 2 / ((n : ℝ) + 2 * numEdges G) ≤ (I.card : ℝ)) := by sorry

end MinDegST.AddOne
