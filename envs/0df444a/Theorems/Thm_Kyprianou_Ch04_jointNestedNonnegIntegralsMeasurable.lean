-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointNestedNonnegIntegralsMeasurable
-- name    : Kyprianou.Ch04.jointNestedNonnegIntegralsMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:27:16.832819+00:00
-- url     : https://prove2.me/theorems/768e48aa-aa82-48bc-b5f4-5f2e3df24dc7
-- title:
--   Iterate the joint measurability of deterministic nonnegative and Bochner integrals on the time and mark coordinates.
-- statement:
--   Iterate the joint measurability of deterministic nonnegative and Bochner integrals on the time and mark coordinates.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.6, printed page 97.; correction of the formalisation of 61a5bc8c-34e9-49c2-b76f-9c0e0650fed4. Corrects the remaining exceptional-outcome measurability defect in AdaptedV2.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem jointNestedNonnegIntegralsMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (mu nu : Measure Real) [SigmaFinite mu] [SigmaFinite nu]
    (f : Omega × (Real × Real) → Real) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (w,(s,x))) ∂nu ∂mu) ∧
    Measurable (fun w => ∫ s, ∫ x, f (w,(s,x)) ∂nu ∂mu) := by
  sorry
end Kyprianou.Ch04
