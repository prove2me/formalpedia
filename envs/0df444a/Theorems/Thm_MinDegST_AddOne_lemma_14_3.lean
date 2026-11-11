-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_14_3
-- name    : MinDegST.AddOne.lemma_14_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:54:05.317233+00:00
-- url     : https://prove2.me/theorems/baf9f36b-b737-4d3c-b3f9-85f8df1246b3
-- title:
--   Lemma 14.3 — a θ-molecular decomposition in O(n) time
-- statement:
--   Let $G$ be a connected graph on $n$ nodes, $k<n$ a threshold for which $G$ has a spanning tree of maximum degree at most $k$, $F$ a forest of $G$ of maximum degree at most $k+1$, and $\theta$ an integer with $1\le\theta\le n$. One deterministic word-RAM program and a constant $K>0$ do the following: on input $(n,k,\theta,F)$ halt within
--   $$K\cdot n+K$$
--   steps and output a $\theta$-molecular decomposition of $F$ (Definition 14.2) as a list of distinct molecules.
--
--   Cited from [BFW26]; it builds the decomposition with $\theta=\lceil 10n/f\rceil$ in step 1 of Theorem 13.1's execution.
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: O(n) → ∃ K > 0: cost ≤ K·n + K; reason: explicit constant
--   - encoding: given a feasible forest F with n vertices and θ; obtains a θ-molecular decomposition → input [n, k, θ, |E(F)|, F's edge list] in any order; output the molecules, each once, as triples [0, x, y] (T^F_{x←y}) or [1, r, r] (special, root r); reason: a concrete input/output layout for the RAM
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 37, Lemma 14.3

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_MinDegST_AddOne_Molecules
import Definitions.Def_MinDegST_AddOne_Inputs

namespace MinDegST.AddOne

/-- **Lemma 14.3** ([BFW26], threshold form). One deterministic word-RAM program and a constant
`K > 0` such that: for every connected simple graph `G` on `Fin n`, every threshold `k < n` for which
`G` has a spanning tree of maximum degree `≤ k`, every forest `F` of `G` of maximum degree `≤ k + 1`
(edge list `fs`) and every integer `θ ∈ [1, n]`, on input `(n, k, θ, fs)` the program halts within
`K · n + K` steps and outputs a `θ`-molecular decomposition of `F` (a list of distinct molecules). -/
theorem lemma_14_3 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n))
        (fs : List (Fin n × Fin n)) (θ : ℕ),
        G.Connected → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 1 ≤ θ → θ ≤ n →
          WordBounded P (encThetaInput n k θ fs) width n ∧
          HaltsWithin P (encThetaInput n k θ fs) (K * (n : ℝ) + K)
            (fun out => ∃ lM : List (Molecule n), lM.Nodup ∧ out = encMolecules lM ∧
              IsThetaDecomp F k θ lM.toFinset) := by sorry

end MinDegST.AddOne
