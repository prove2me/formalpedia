-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_14_4
-- name    : MinDegST.AddOne.lemma_14_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:53.675204+00:00
-- url     : https://prove2.me/theorems/86a1cd24-4ef8-4cdf-a4e5-b30315ed1b1f
-- title:
--   Lemma 14.4 — degree reduction inside a reducible region in Õ(|E(G[V(C)])|) time
-- statement:
--   Let $G$ be a connected graph on $n$ nodes, $k<n$ a threshold for which $G$ has a spanning tree of maximum degree at most $k$, $F$ a forest of $G$ with maximum degree at most $k+1$, $M$ a molecular decomposition of $F$ with reducible regions $\mathcal R$, $C\in\mathcal R$ and $u\in V(C)$. There is one deterministic word-RAM program (the degree-reduction subroutine) and constants $K>0$, $c$ such that, handed the local data of $C$ (its nodes with their forest degrees, the edges of $G[V(C)]$ and of $F[V(C)]$), it halts within
--   $$K\cdot|E(G[V(C)])|\cdot(\log_2(n+2))^c+K$$
--   steps and outputs the edges inside $V(C)$ of a forest $F^+$ of $G$ that agrees with $F$ outside $V(C)$, with $\deg_{F^+}(u)\le k$ and $F^+$ of maximum degree at most $k+1$.
--
--   This is the Fürer–Raghavachari local improvement step, cited from [BFW26, Lemma 2.1]: it is how a node of a reducible region is made slack, the elementary move of every alternation.
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: Õ(|E(G[V(C)])|) (polylog factors in n hidden) → ∃ K > 0, c ∈ ℕ: cost ≤ K·|E(G[V(C)])|·(log₂(n + 2))^c + K; reason: explicit constants for the asymptotic notation; the additive K covers tiny inputs
--   - reading: the subroutine runs in Õ(|E(G[V(C)])|) time on F, C, u (input representation unspecified) → the program is handed n, k, u, the node list of C with forest degrees, the edge list of G[V(C)] and the edge list of F[V(C)], and outputs the new edges of F inside V(C); reason: a time bound below the size of the whole input only has a meaning once the local data the subroutine sees is fixed
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 38, Lemma 14.4

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_MinDegST_AddOne_Molecules
import Definitions.Def_MinDegST_AddOne_Inputs

namespace MinDegST.AddOne

/-- **Lemma 14.4** ([BFW26, Lemma 2.1], threshold form). One deterministic word-RAM program (the
degree-reduction subroutine) and constants `K > 0`, `c` such that: for every connected simple graph
`G` on `Fin n`, every threshold `k < n` for which `G` has a spanning tree of maximum degree `≤ k`,
every forest `F` of `G` of maximum degree `≤ k + 1`, every molecular decomposition `M` of `F` with
its reducible regions `𝓡`, every region `C ∈ 𝓡` and every `u ∈ V(C)`: handed the local data of `C`
(its node list `vs` with their `F`-degrees, the edge list `gs` of `G[V(C)]` and the edge list `fs`
of `F[V(C)]`), the program halts within `K · |E(G[V(C)])| · (log₂(n + 2))^c + K` steps and outputs
the edges inside `V(C)` of a forest `F⁺` of `G` that agrees with `F` on every edge not inside `V(C)`
(so only edges with both endpoints in `V(C)` are inserted or deleted), with
1. `deg_{F⁺}(u) ≤ k`, and 2. `F⁺` of maximum degree `≤ k + 1`. -/
theorem lemma_14_4 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ) (c : ℕ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n))
        (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n))) (C : Finset (Fin n)) (u : Fin n)
        (vs : List (Fin n)) (gs fs : List (Fin n × Fin n)),
        G.Connected → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsMolDecomp F M → IsRegionsOf G F k M 𝓡 →
        C ∈ 𝓡 → u ∈ C →
        vs.Nodup → vs.toFinset = C → IsEdgeListOf (inside G C) gs → IsEdgeListOf (inside F C) fs →
          WordBounded P (encRegionInput n k u F vs gs fs) width (n + numEdges (inside G C)) ∧
          HaltsWithin P (encRegionInput n k u F vs gs fs)
            (K * (numEdges (inside G C) : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ c + K)
            (fun out => ∃ F' : SimpleGraph (Fin n), EncodesEdges out (inside F' C) ∧
              F' \ inside F' C = F \ inside F C ∧
              IsForestOf G F' ∧ deg F' u ≤ k ∧ Feasible k F') := by sorry

end MinDegST.AddOne
