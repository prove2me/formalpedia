-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_msd_solution
-- name    : LangevinHarmonicTrap.msd_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:12:41.100982+00:00
-- url     : https://prove2.me/theorems/95db6b58-1400-46da-82d8-c177b03c9603
-- title:
--   Solution of the MSD equation with $M(0)=\dot M(0)=0$
-- statement:
--   Part (d) of the source. Let $\lambda_\pm$ be two distinct roots of the characteristic polynomial $m\lambda^2 + \zeta\lambda + 2k$ of the MSD equation. Then $$ M(t) = \frac{d\,k_BT}{k}\left[ 1 + \frac{\lambda_- e^{\lambda_+ t} - \lambda_+ e^{\lambda_- t}}{\lambda_+-\lambda_-} \right] $$ is twice differentiable, solves $m\ddot M + \zeta\dot M + 2kM = 2dk_BT$, and starts from rest at the origin: $M(0) = 0$ and $\dot M(0) = 0$ — the initial conditions appropriate to a particle whose displacement is measured from its position at $t=0$.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib

open Real

namespace LangevinHarmonicTrap

theorem msd_solution {d : ℕ} {m zeta k kB T lamP lamM : ℝ}
    (hk : k ≠ 0) (hne : lamP ≠ lamM)
    (hrootP : m * lamP ^ 2 + zeta * lamP + 2 * k = 0)
    (hrootM : m * lamM ^ 2 + zeta * lamM + 2 * k = 0)
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = d * kB * T / k *
      (1 + (lamM * Real.exp (lamP * t) - lamP * Real.exp (lamM * t)) / (lamP - lamM)))
    (hM1 : ∀ t : ℝ, M1 t = d * kB * T / k *
      (lamP * lamM * (Real.exp (lamP * t) - Real.exp (lamM * t)) / (lamP - lamM)))
    (hM2 : ∀ t : ℝ, M2 t = d * kB * T / k *
      (lamP * lamM * (lamP * Real.exp (lamP * t) - lamM * Real.exp (lamM * t))
        / (lamP - lamM))) :
    (∀ t : ℝ, HasDerivAt M (M1 t) t) ∧ (∀ t : ℝ, HasDerivAt M1 (M2 t) t) ∧
      (∀ t : ℝ, m * M2 t + zeta * M1 t + 2 * k * M t = 2 * (d * kB * T)) ∧
      M 0 = 0 ∧ M1 0 = 0 := by sorry

end LangevinHarmonicTrap
