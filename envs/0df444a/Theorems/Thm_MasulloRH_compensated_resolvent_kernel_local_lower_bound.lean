-- Prove2me | Theorems.Thm_MasulloRH_compensated_resolvent_kernel_local_lower_bound
-- name    : MasulloRH.compensated_resolvent_kernel_local_lower_bound
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T00:00:46.581234+00:00
-- url     : https://prove2.me/theorems/91876255-f892-41f1-b564-3653ab2f5a3f
-- title:
--   Compensated shifted resolvent has a local 3/10 lower bound
-- statement:
--   Under the hypotheses of the high-height compensated-resolvent estimate, if the probe is within one unit of the zero height, $|T-\gamma|\le1$, then the same kernel satisfies
--
--   $$k_T(\rho)\ge\frac{3}{10}.$$
--
--   Indeed the first resolvent term is at least $3/10$ on $2\le a\le3$, while the compensation term is nonnegative by the preceding arithmetic estimate. This is the local mass estimate needed before one can sum over zeros in a unit-height window. It remains independent of the regularized trace and makes no Riemann-hypothesis assumption.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1 (20 November 2026 draft), together with the compensated-resolvent proposal in the Prove2Me Masullo mission discussion, comment ad8fb92e-0c03-4bee-937c-638f829135a3.

import Mathlib

theorem MasulloRH.compensated_resolvent_kernel_local_lower_bound (β γ T : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 36 ≤ γ ^ 2) (hnear : |T - γ| ≤ 1) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
    (3 / 10 : ℝ) ≤ k := by sorry
