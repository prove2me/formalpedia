-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_msd_overdamped
-- name    : LangevinHarmonicTrap.msd_overdamped
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:13:00.95644+00:00
-- url     : https://prove2.me/theorems/095e51e1-1bb8-4b7f-b876-d3ff9f0d69db
-- title:
--   Overdamped MSD: $M(t) = \frac{dk_BT}{k}\left(1-e^{-2kt/\zeta}\right)$ and its plateau
-- statement:
--   Part (e) of the source, in the inertialess regime $m \to 0$ where the MSD equation reduces to $\zeta \dot M + 2kM = 2dk_BT$. Its solution starting from $M(0)=0$ is $$ M(t) = \frac{d k_B T}{k}\left(1 - e^{-2kt/\zeta}\right), $$ whose initial slope $\dot M(0) = 2 d k_B T/\zeta = 2 d D$ is the free-diffusion law with $D = k_B T/\zeta$, and which saturates as $t \to \infty$ at the equipartition plateau $d k_B T/k$; the crossover occurs on the trap relaxation time $\zeta/(2k)$.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib

open Real Filter Topology

namespace LangevinHarmonicTrap

theorem msd_overdamped {d : ℕ} {zeta k kB T : ℝ} (hzeta : 0 < zeta) (hk : 0 < k)
    (M M1 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = d * kB * T / k * (1 - Real.exp (-(2 * k / zeta) * t)))
    (hM1 : ∀ t : ℝ, M1 t = 2 * (d * kB * T) / zeta * Real.exp (-(2 * k / zeta) * t)) :
    (∀ t : ℝ, HasDerivAt M (M1 t) t) ∧
      (∀ t : ℝ, zeta * M1 t + 2 * k * M t = 2 * (d * kB * T)) ∧
      M 0 = 0 ∧ M1 0 = 2 * (d * kB * T) / zeta ∧
      Tendsto M atTop (𝓝 (d * kB * T / k)) := by sorry

end LangevinHarmonicTrap
