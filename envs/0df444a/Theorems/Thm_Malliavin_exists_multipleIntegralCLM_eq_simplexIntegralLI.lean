-- Prove2me | Theorems.Thm_Malliavin_exists_multipleIntegralCLM_eq_simplexIntegralLI
-- name    : Malliavin.exists_multipleIntegralCLM_eq_simplexIntegralLI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:24.555081+00:00
-- url     : https://prove2.me/theorems/b9a30e6b-110f-48c1-94f3-1a59754e975a
-- title:
--   Malliavin: exists multiple Integral CLM eq simplex Integral LI
-- statement:
--   Every vector in the `n + 1` simplex summand of the global positive tower is the value of the
--   selected order-`n + 1` multiple operator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L106-L121
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L106-L121

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.exists_multipleIntegralCLM_eq_simplexIntegralLI
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (g : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∃ f : IteratedKernel (n + 1),
      multipleIntegralCLM hB (n + 1) f =
        IteratedIntegralConstruction.simplexIntegralLI hB n g := by sorry
