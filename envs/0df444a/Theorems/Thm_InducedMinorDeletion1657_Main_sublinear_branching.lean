-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_sublinear_branching
-- name    : InducedMinorDeletion1657.Main.sublinear_branching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:27.022872+00:00
-- url     : https://prove2.me/theorems/24688010-e46c-4a32-a34a-89c83dedc6b8
-- title:
--   Theorem 4.1 — sublinear-treewidth branching
-- statement:
--   Fix $H$. One algorithm and positive constants, depending only on $H$, work on every $H$-induced-minor-free graph $G$ with positive parameters $k,d,t$ and $d>2t$. They produce subsets $X_1,\dots,X_r$ with
--   $$r\le C(k+2)^{C(t+1)^ak/d},\quad T\le C(k+2)^{C(t+1)^ak/d}(n+1)^c,$$
--   $$\operatorname{tw}(G-X_i)\le Ct^a\sqrt{kd}\quad\text{for every }i.$$
--   Every treewidth-$t$ modulator $S$ of size at most $k$ contains one of the produced $X_i$. Neither an unknown modulator nor a decomposition is supplied. Both clauses are retained with their full parameter dependence.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite published register program, actual halting iteration, output charge and logarithmically bounded words; reason: operational word-RAM reading; constants and the program precede every varying graph and numerical input
--   - encoding: O notation and small input bases n, k → positive uniform constants, n+1 and k+2, and an upper bound on collection size; reason: makes source asymptotics pointwise at small inputs without changing any unbounded parameter dependence
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 16 (PDF p. 17), Theorem 4.1

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Theorem 4.1, printed p. 16 / PDF p. 17. See the local source audit for conventions. -/
theorem sublinear_branching :
∀ H : InputGraph, ∃ (P : Program) (C a c q : ℕ),
  0 < C ∧ 0 < a ∧ 0 < c ∧ 0 < q ∧
  ∀ (G : InputGraph) (k d t : ℕ),
    excluded H.graph G.graph → 0 < k → 0 < t → 2*t < d →
    ∃ L : List (Finset (Fin G.n)), sublinearResult G k d t C a L ∧
      (L.length : ℝ) ≤ branchCount C a k d t ∧
      ramOutputs P (k :: d :: t :: graphWords G) (familyWords L)
        (branchTime C a c G.n k d t) q := by sorry

end InducedMinorDeletion1657.Main
