-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_treewidth_modulator_approximation
-- name    : InducedMinorDeletion1657.Main.treewidth_modulator_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:03.273215+00:00
-- url     : https://prove2.me/theorems/9212ccff-2d7b-4e6b-90a2-2308d9a0d8da
-- title:
--   Lemma 3.8 — treewidth-modulator approximation (corrected: t=1 logarithm)
-- statement:
--   For every graph $G$ on $n$ vertices and positive integer $t$, compute a treewidth-$t$ modulator $S$. If $k$ is the minimum cardinality of any treewidth-$t$ modulator, then
--   $$|S|\le Ck\log_2\max(2,t),\qquad T\le C2^{C(t+1)^a}(n+1)^c.$$
--   One program and positive constants $C,a,c,q$ work for all graphs and all $t$. The parameter $k$ is computed mathematically from the graph, not supplied to the program. This supplies the approximate modulator used by core branching.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
--   - correction: O(k log t) at t = 1 → O(k log₂(max(2,t))); reason: K₃ at t=1 has minimum modulator size one, while the unsaturated logarithm forces the impossible empty modulator
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 14 (PDF p. 15), Lemma 3.8

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.8, printed p. 14 / PDF p. 15. See the local source audit for conventions. -/
theorem treewidth_modulator_approximation :
∃ (P : Program) (C a c q : ℕ), 0 < C ∧ 0 < a ∧ 0 < c ∧ 0 < q ∧
  ∀ (G : InputGraph) (t : ℕ), 0 < t →
  ∃ S : Finset (Fin G.n), modulator G.graph t S ∧
    (S.card : ℝ) ≤ C * modOpt G.graph t * satLog t ∧
    ramOutputs P (t :: graphWords G) (subsetWords S)
      (polyTime C c G.n * (2 : ℝ) ^ (C * ((t : ℝ) + 1) ^ a)) q := by sorry

end InducedMinorDeletion1657.Main
