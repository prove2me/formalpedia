-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
-- name    : Kyprianou.Ch04.ito43_levy_jump_energy_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:21:59.436849+00:00
-- url     : https://prove2.me/theorems/4a5a0450-c670-5b77-8a5e-f5167cfcef1b
-- title:
--   Almost sure square summability and localisation of actual Levy jump energy
-- statement:
--   The squared actual jumps of a general real Levy process are almost surely summable on a positive compact horizon, and their energy has arbitrarily small outer probability tails.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Square-summability and outer probability localisation of the actual jump energy. -/

theorem Kyprianou.Ch04.ito43_levy_jump_energy_localisation {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (T : NNReal) (hT : 0 < T) :
    let J : Ω → (Ioc (0 : NNReal) T → ℝ) := fun w t => (X t w-L t w)^2
    (∀ᵐ w ∂P, Summable (J w)) ∧
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
        (P {w | ¬ Summable (J w) ∨ C < ∑' t, J w t}).toReal ≤ η := by sorry
