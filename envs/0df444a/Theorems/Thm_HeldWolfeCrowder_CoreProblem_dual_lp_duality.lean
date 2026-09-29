-- Prove2me | Theorems.Thm_HeldWolfeCrowder_CoreProblem_dual_lp_duality
-- name    : HeldWolfeCrowder.CoreProblem.dual_lp_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:50:30.024784+00:00
-- url     : https://prove2.me/theorems/f2b316c7-3958-4631-b60b-1bb58c12cb8c
-- title:
--   Eq. (6.1) — LP duality: (6.1) has a solution and its value is max w
-- statement:
--   Let $w(\pi)=\min_k\{c_k+\pi\cdot v_k\}$ on $E^n$ be bounded above. Writing $\max_\pi w(\pi)$ as the linear program $\max\{z : z-\pi\cdot v_k\le c_k \text{ for all } k\}$, its dual is
--   $$\min\Big\{\sum_k c_k y_k : y_k\ge0,\ \sum_k y_k=1,\ \sum_k -v_k y_k=0\Big\}. \tag{6.1}$$
--   The duality theorem of linear programming gives: $w$ attains its maximum at some $\pi^*$, (6.1) has an optimal solution $y$, and
--   $$\sum_k c_k y_k=w(\pi^*)=\max w.$$
--
--   This identifies the target value of the subgradient method with the optimal value of (6.1); Theorem 6.3 then shows that a finite linear program built from the iterates attains it.
--
--   **Formalization Note** The equality constraint is written $\sum_k y_k v_k=0$. The conclusion bundles attainment of $\max w$, existence of a solution of (6.1), and equality of the two optimal values.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 81, Eq. (6.1)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Held, Wolfe & Crowder (1974), Eq. (6.1), p. 81.** Linear-programming duality between
`max w` (the problem `max {z : z − π·v_k ≤ c_k for all k}`) and its dual (6.1): if `w` is
bounded above, then `w` attains its maximum at some `π*`, (6.1) has an optimal solution `y`,
and the two optimal values agree, `Σ_k c_k y_k = w(π*) = max w`. -/
theorem dual_lp_duality {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v))) :
    ∃ (πstar : EuclideanSpace ℝ (Fin n)) (y : ι → ℝ),
      (∀ π', w c v π' ≤ w c v πstar) ∧ IsDualOptimal c v y ∧ dualObj c y = w c v πstar := by sorry

end HeldWolfeCrowder.CoreProblem
