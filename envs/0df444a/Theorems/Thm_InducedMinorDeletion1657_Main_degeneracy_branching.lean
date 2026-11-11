-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_degeneracy_branching
-- name    : InducedMinorDeletion1657.Main.degeneracy_branching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:50.292457+00:00
-- url     : https://prove2.me/theorems/8ef40e12-c47e-4e96-9a40-f603ca0af080
-- title:
--   Lemma 4.3 — degeneracy branching
-- statement:
--   Given $G$ and positive integers $\Delta\ge t$, compute subsets $A_1,\dots,A_r$ with time and count bounded by
--   $$C(n+1)^{Ct^2n/\Delta}.$$
--   For each $A_i$ there exists $B_i\subseteq V(G)\setminus A_i$ such that $G[B_i]$ is $t$-degenerate and every vertex outside $A_i\cup B_i$ has degree at most $\Delta$ in $G-A_i$. Also $G-A_i$ is $\Delta$-degenerate. For every subset $S$ with $G-S$ $t$-degenerate there is an $i$ with $A_i\subseteq S$. Degeneracy means the usual every-nonempty-subgraph condition. This is the entire branching guarantee, including its separate degree witness.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
--   - encoding: satisfying that and G−S is t-degenerate → G−S is t-degenerate; reason: the stray words that and are a typographical artifact with no mathematical condition
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 17 (PDF p. 18), Lemma 4.3

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 4.3, printed p. 17 / PDF p. 18. See the local source audit for conventions. -/
theorem degeneracy_branching :
∃ (P : Program) (C q : ℕ), 0 < C ∧ 0 < q ∧
  ∀ (G : InputGraph) (Δ t : ℕ), 0 < t → t ≤ Δ →
    ∃ L : List (Finset (Fin G.n)), degeneracyResult G Δ t L ∧
      (L.length : ℝ) ≤ degenCount C G.n Δ t ∧
      ramOutputs P (Δ :: t :: graphWords G) (familyWords L)
        (degenCount C G.n Δ t) q := by sorry

end InducedMinorDeletion1657.Main
