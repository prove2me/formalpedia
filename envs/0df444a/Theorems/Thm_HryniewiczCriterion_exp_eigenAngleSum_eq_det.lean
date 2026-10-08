-- Prove2me | Theorems.Thm_HryniewiczCriterion_exp_eigenAngleSum_eq_det
-- name    : HryniewiczCriterion.exp_eigenAngleSum_eq_det
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:47:30.642603+00:00
-- url     : https://prove2.me/theorems/152d4ebd-ca08-4d9c-8b5d-4b12c5b1111c
-- title:
--   The eigen-angle sum exponentiates to the determinant
-- statement:
--   For a complex square matrix $V$ with $|\det V|=1$ (e.g. unitary),
--   $$\exp\Big(i\sum_{\lambda}\operatorname{ang}(\lambda)\Big)\;=\;\det V,$$
--   the sum running over the eigenvalues of $V$ with algebraic multiplicity, $\operatorname{ang}\in(0,2\pi]$ the normalized argument (`angPos`). In particular $\theta-\mathrm{eigenAngleSum}\,V\in2\pi\mathbb{Z}$ whenever $e^{i\theta}=\det V$.
--   Proof idea: $e^{i\operatorname{ang}(z)}=z/|z|$; multiply over the roots of the characteristic polynomial, whose product is $\det V$ and whose absolute values multiply to $|\det V|=1$.
-- source:
--   Elementary; bookkeeping for the eigen-angle count in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion

theorem HryniewiczCriterion.exp_eigenAngleSum_eq_det {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (hV : ‖V.det‖ = 1) :
    Complex.exp ((eigenAngleSum V : ℂ) * Complex.I) = V.det := by sorry
