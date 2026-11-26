-- Prove2me | Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
-- name    : Kyprianou.Ch04.completedMeasAECongrV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:44.662115+00:00
-- url     : https://prove2.me/theorems/84806742-2031-5e30-b0e1-b24dfdfc9a01
-- title:
--   Completed natural filtration measurability of almost sure versions
-- statement:
--   Completed natural filtration measurability of almost sure versions
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem completedMeasAECongrV1 {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (t : NNReal) (W V : Ω → E) (hV : Measurable[F t] V) (hWV : W =ᵐ[P] V) :
    Measurable[F t] W := by
  sorry
end Kyprianou.Ch04
