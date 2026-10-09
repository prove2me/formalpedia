-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_matroid_ocrs
-- name    : OnlineCRS.Matroid.matroid_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:08.071988+00:00
-- url     : https://prove2.me/theorems/267ded6c-4ca5-4ad9-9fc6-36d4266660c4
-- title:
--   Theorem 2.1 — a deterministic (b, 1−b)-selectable greedy OCRS for loopless matroids
-- statement:
--   Let $M$ be a finite loopless matroid on $N$, and let $P_{\mathcal F}$ be its matroid independence polytope. For every $b\in[0,1]$, there exists a deterministic greedy OCRS for $P_{\mathcal F}$ such that for every $x\in bP_{\mathcal F}$ and $e\in N$,
--   $$\Pr\bigl[I\cup\{e\}\in\mathcal F_x\text{ for every }I\subseteq R(x)\text{ with }I\in\mathcal F_x\bigr]\ge 1-b.$$
--
--   This gives an arrival-order-independent selectability guarantee for matroid constraints. The printed theorem is false for looped matroids when $b<1$; the loopless condition is the disclosed correction, and the empty greedy family is excluded by definition.
-- source:
--   arXiv:1508.00142v2, Theorem 2.1, p. 9 (loopless correction)

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Polytope

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, Theorem 2.1, p. 9, with the disclosed loopless correction. -/
theorem matroid_ocrs {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) [M.Loopless]
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ fam : (α → ℝ) → Finset (Finset α),
      IsSelectableDet (fun I : Finset α => M.Indep (I : Set α))
        (matroidPolytope M) b (1 - b) fam := by sorry

end OnlineCRS.Matroid
