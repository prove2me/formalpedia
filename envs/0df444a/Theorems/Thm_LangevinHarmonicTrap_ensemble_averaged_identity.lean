-- Prove2me | Theorems.Thm_LangevinHarmonicTrap_ensemble_averaged_identity
-- name    : LangevinHarmonicTrap.ensemble_averaged_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:12:01.460983+00:00
-- url     : https://prove2.me/theorems/e4c8536c-7b24-4747-9193-f4eb6a044683
-- title:
--   Ensemble average of the pathwise identity over a probability space of paths
-- statement:
--   The averaging step of part (b), before the two physical inputs are used. Let the paths be indexed by a probability space $(\Omega,\mu)$, and let $M = \langle r^2\rangle$, $M_1 = \langle \dot{(r^2)}\rangle$, $M_2 = \langle \ddot{(r^2)}\rangle$ be the ensemble averages of the pathwise squared displacement and of its first two time derivatives. Then $$ \frac{m}{2} M_2(t) + \frac{\zeta}{2} M_1(t) + k\,M(t) = m\,\langle \dot r(t)^2\rangle + \langle r(t)\cdot f(t)\rangle . $$ Only linearity of the average and integrability of the averaged quantities are used here; the thermal assumptions enter at the next step.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib
import Definitions.Def_LangevinHarmonicTrap_dotSum
import Definitions.Def_LangevinHarmonicTrap_IsLangevinPath

open Finset MeasureTheory

namespace LangevinHarmonicTrap

theorem ensemble_averaged_identity {d : ℕ} {m zeta k : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {x v a f : Ω → Fin d → ℝ → ℝ}
    (hdyn : ∀ w : Ω, IsLangevinPath d m zeta k (x w) (v w) (a w) (f w))
    (M M1 M2 : ℝ → ℝ)
    (hM : ∀ t : ℝ, M t = ∫ w, dotSum d (x w) (x w) t ∂mu)
    (hM1 : ∀ t : ℝ, M1 t = ∫ w, 2 * dotSum d (x w) (v w) t ∂mu)
    (hM2 : ∀ t : ℝ, M2 t = ∫ w, 2 * (dotSum d (v w) (v w) t + dotSum d (x w) (a w) t) ∂mu)
    (hxx : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (x w) t) mu)
    (hxv : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (v w) t) mu)
    (hvv : ∀ t : ℝ, Integrable (fun w => dotSum d (v w) (v w) t) mu)
    (hxa : ∀ t : ℝ, Integrable (fun w => dotSum d (x w) (a w) t) mu) :
    ∀ t : ℝ, m / 2 * M2 t + zeta / 2 * M1 t + k * M t
      = m * (∫ w, dotSum d (v w) (v w) t ∂mu) + ∫ w, dotSum d (x w) (f w) t ∂mu := by sorry

end LangevinHarmonicTrap
