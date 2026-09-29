-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_msd_ode
-- name    : LangevinHarmonicTrap.msd_ode
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:12:28.420728+00:00
-- url     : https://prove2.me/theorems/8b901f3e-d197-4de3-a220-84c390c43f73
-- title:
--   The MSD equation $m\ddot M + \zeta \dot M + 2kM = 2dk_BT$
-- statement:
--   The goal of the mission, part (b) of the source. For an ensemble of realizations of Newton's equation $m\ddot r = -\zeta \dot r - k r + f$, assume with Langevin that ensemble averaging commutes with time differentiation, that the random force is uncorrelated with the instantaneous position, $\langle r\cdot f\rangle = 0$, and that the velocity is thermalized, $m\langle \dot r^2\rangle = d\,k_B T$. Then the mean-squared displacement $M(t) = \langle r(t)^2 \rangle$ obeys the closed, deterministic, linear equation $$ m\,\ddot M(t) + \zeta\,\dot M(t) + 2k\,M(t) = 2 d\, k_B T . $$
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib
import Definitions.Def_LangevinHarmonicTrap_dotSum
import Definitions.Def_LangevinHarmonicTrap_IsLangevinPath

open Finset MeasureTheory

namespace LangevinHarmonicTrap

theorem msd_ode {d : ℕ} {m zeta k kB T : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {x v a f : Ω → Fin d → ℝ → ℝ}
    (hdyn : ∀ w : Ω, IsLangevinPath d m zeta k (x w) (v w) (a w) (f w))
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = ∫ w, dotSum d (x w) (x w) t ∂mu)
    (hM1 : ∀ t : ℝ, M1 t = ∫ w, 2 * dotSum d (x w) (v w) t ∂mu)
    (hM2 : ∀ t : ℝ, M2 t = ∫ w, 2 * (dotSum d (v w) (v w) t + dotSum d (x w) (a w) t) ∂mu)
    (hMderiv : ∀ t : ℝ, HasDerivAt M (M1 t) t)
    (hM1deriv : ∀ t : ℝ, HasDerivAt M1 (M2 t) t)
    (hxx : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (x w) t) mu)
    (hxv : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (v w) t) mu)
    (hvv : ∀ t : ℝ, Integrable (fun w => dotSum d (v w) (v w) t) mu)
    (hxa : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (a w) t) mu)
    (hnoise : ∀ t : ℝ, ∫ w, dotSum d (x w) (f w) t ∂mu = 0)
    (hequip : ∀ t : ℝ, m * ∫ w, dotSum d (v w) (v w) t ∂mu = d * kB * T) :
    ∀ t : ℝ, m * deriv (deriv M) t + zeta * deriv M t + 2 * k * M t
      = 2 * (d * kB * T) := by sorry

end LangevinHarmonicTrap
