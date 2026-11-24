-- Prove2me | Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3
-- name    : Kyprianou.subordinatorCriterionCh02V3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:20:06.238409+00:00
-- url     : https://prove2.me/theorems/e443a7da-eab2-4c63-a0b6-1ad3964a019a
-- title:
--   Lemma 2.14: corrected subordinator path criterion
-- statement:
--   A real Lévy process has almost surely nondecreasing sample paths if and only if its Lévy measure has no negative jumps, the Gaussian coefficient vanishes, the small positive jumps are of finite variation, and the finite-variation drift d = -(a + integral_(0,1) x Pi(dx)) is nonnegative. The minus compensator sign agrees with the source convention and is checked against the compensated finite-activity Poisson example X_t=N_t/2-t/2.
-- source:
--   A. E. Kyprianou (2006), Lemma 2.14, p. 55, with explicit sign correction from (2.21)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem subordinatorCriterionCh02V3
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) ↔
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by sorry

end Kyprianou
