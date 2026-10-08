-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_tK_facts
-- name    : HessianDamping.IGAHD.tK_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:03.829258+00:00
-- url     : https://prove2.me/theorems/179fbf46-b1a5-44b6-a728-aa6042a3c817
-- title:
--   §3.2, pp. 15–16 — identities for t_k
-- statement:
--   For $\alpha\ge3$, define $t_k=(k-1)/(\alpha-1)$. Then for every integer $k\ge1$,
--
--   $$t_k=1+t_{k+1}(1-\alpha/k),\qquad t_{k+1}^2-t_{k+1}-t_k^2\le0.$$
--
--   These two facts connect the paper's time coefficients with the algorithmic momentum and the energy comparison.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, pp. 15–16, t_k identity and inequality in proof of Theorem 6

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- The t_k identities used on pp. 15–16. -/
theorem tK_facts (α : ℝ) (hα : 3 ≤ α) (k : ℕ) (hk : 1 ≤ k) :
    tK α k = 1 + tK α (k + 1) * (1 - α / (k : ℝ)) ∧
    tK α (k + 1) ^ 2 - tK α (k + 1) - tK α k ^ 2 ≤ 0 := by sorry
end HessianDamping.IGAHD
