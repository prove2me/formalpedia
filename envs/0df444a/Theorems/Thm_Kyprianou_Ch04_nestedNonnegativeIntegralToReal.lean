-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nestedNonnegativeIntegralToReal
-- name    : Kyprianou.Ch04.nestedNonnegativeIntegralToReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:27:13.782362+00:00
-- url     : https://prove2.me/theorems/d8fbc7a0-564d-44af-a841-cde314267e7a
-- title:
--   Finite iterated nonnegative mass makes the inner extended integral finite almost everywhere. Convert the inner integrals pointwise and then convert the outer integral.
-- statement:
--   Finite iterated nonnegative mass makes the inner extended integral finite almost everywhere. Convert the inner integrals pointwise and then convert the outer integral.
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
theorem nestedNonnegativeIntegralToReal
    (mu nu : Measure Real) [SigmaFinite nu]
    (f : Real × Real → Real) (hf : Measurable f) (hn : ∀ z, 0 ≤ f z)
    (hFin : (∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (s,x)) ∂nu ∂mu) ≠ ⊤) :
    (∫ s, ∫ x, f (s,x) ∂nu ∂mu) =
      (∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (s,x)) ∂nu ∂mu).toReal := by
  sorry
end Kyprianou.Ch04
