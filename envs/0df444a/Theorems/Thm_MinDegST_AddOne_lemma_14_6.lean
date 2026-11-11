-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_14_6
-- name    : MinDegST.AddOne.lemma_14_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:57.841798+00:00
-- url     : https://prove2.me/theorems/714d633d-1ed7-4755-b564-650425c28daa
-- title:
--   Lemma 14.6 — all reducible regions of a molecule in Õ(Σ deg_G) time, and of the whole decomposition in Õ(m)
-- statement:
--   Let $G$ be a connected graph with $n$ nodes and $m$ edges, $k<n$ a threshold for which $G$ has a spanning tree of maximum degree at most $k$, and $F$ a forest of $G$ of maximum degree at most $k+1$.
--   1. One deterministic word-RAM program and constants $K>0$, $c$: for every molecule $\mu$ of $F$, handed the local data of $\mu$, it halts within
--   $$K\cdot\Big(\sum_{v\in V(\mu)}\deg_G(v)\Big)\cdot(\log_2(n+2))^c+K$$
--   steps and outputs all reducible regions inside $\mu$ (a final state of the region procedure on $\mu$).
--   2. One deterministic word-RAM program and constants $K>0$, $c$: for every molecular decomposition $M$ of $F$, on input $(G,k,F,M)$ it halts within $K\cdot m\cdot(\log_2(n+2))^c+K$ steps and outputs the set of all $M$-reducible regions.
--
--   Cited from [BFW26]; the regions are the contracted vertices of the path-encoding graph.
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: Õ(Σ_{v∈V(M)} deg_G(v)) (polylog factors in n hidden) → ∃ K > 0, c ∈ ℕ: cost ≤ K·Σ_{v∈V(M)} deg_G(v)·(log₂(n + 2))^c + K; reason: explicit constants for the asymptotic notation; the additive K covers tiny inputs
--   - encoding: Õ(m) (polylog factors in n hidden) → ∃ K > 0, c ∈ ℕ: cost ≤ K·m·(log₂(n + 2))^c + K; reason: explicit constants for the asymptotic notation; the additive K covers tiny inputs
--   - reading: for any molecule M, its regions in Õ(Σ_{v∈V(M)} deg_G(v)) time (input representation unspecified) → the program is handed n, k, the node list of the molecule with each node's forest degree, G-degree and G-adjacency list, and the edge list of F inside the molecule; reason: a time bound below the size of the whole input only has a meaning once the local data is fixed
--   - encoding: all regions over the entire decomposition → input [graph edge list, k, forest edge list, decomposition as a molecule list]; output the regions as a family of node lists; reason: a concrete input/output layout for the RAM
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 38, Lemma 14.6

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_MinDegST_AddOne_Molecules
import Definitions.Def_MinDegST_AddOne_Inputs

namespace MinDegST.AddOne

/-- **Lemma 14.6** ([BFW26], threshold form). Two deterministic word-RAM programs.
1. (One molecule.) Constants `K > 0`, `c` such that: for every connected `G` on `Fin n`, threshold
   `k < n` for which `G` has a spanning tree of maximum degree `≤ k`, forest `F` of `G` of maximum
   degree `≤ k + 1` and molecule `μ` of `F`, handed the local data of `μ` (its node list `vs`, for
   each node its `F`-degree and `G`-adjacency list `nb v`, and the edge list `fs` of `F` inside `μ`),
   the program halts within `K · (Σ_{v ∈ V(μ)} deg_G(v)) · (log₂(n + 2))^c + K` steps and outputs all
   reducible regions inside `μ` (a final state of the region procedure of §14.2 on `μ`).
2. (All molecules.) Constants `K > 0`, `c` such that, for the same `G`, `k`, `F` and every molecular
   decomposition `M` of `F`, on input (graph, `k`, forest, `M`) the program halts within
   `K · m · (log₂(n + 2))^c + K` steps and outputs the set of all `M`-reducible regions. -/
theorem lemma_14_6 :
    (∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ) (c : ℕ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n)) (μ : Molecule n)
        (vs : List (Fin n)) (nb : Fin n → List (Fin n)) (fs : List (Fin n × Fin n)),
        G.Connected → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → μ.IsOf F →
        vs.Nodup → vs.toFinset = μ.verts F → IsAdjListsOf G nb →
        IsEdgeListOf (inside F (μ.verts F)) fs →
          WordBounded P (encMoleculeInput n k F vs nb fs) width n ∧
          HaltsWithin P (encMoleculeInput n k F vs nb fs)
            (K * ((∑ v ∈ μ.verts F, deg G v : ℕ) : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ c + K)
            (fun out => ∃ 𝓡 : Finset (Finset (Fin n)), EncodesFamily out 𝓡 ∧
              RegionOutcome G F k (μ.verts F) 𝓡)) ∧
    (∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ) (c : ℕ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
        (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)) (lM : List (Molecule n)),
        G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsEdgeListOf F fs →
        lM.Nodup → IsMolDecomp F lM.toFinset →
          WordBounded P (encDecompInput n es k fs lM) width (n + es.length) ∧
          HaltsWithin P (encDecompInput n es k fs lM)
            (K * (es.length : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ c + K)
            (fun out => ∃ 𝓡 : Finset (Finset (Fin n)), EncodesFamily out 𝓡 ∧
              IsRegionsOf G F k lM.toFinset 𝓡)) := by sorry

end MinDegST.AddOne
