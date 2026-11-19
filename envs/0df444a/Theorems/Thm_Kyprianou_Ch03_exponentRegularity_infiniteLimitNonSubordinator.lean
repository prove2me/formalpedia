-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentRegularity_infiniteLimitNonSubordinator
-- name    : Kyprianou.Ch03.exponentRegularity_infiniteLimitNonSubordinator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:15.386807+00:00
-- url     : https://prove2.me/theorems/00b8bd20-5648-4ad1-ae9f-cb8a88f4c6c6
-- title:
--   Exercise 3.5 part 5: infiniteLimitNonSubordinator
-- statement:
--   The full original mathematical subpart 5 of Exercise 3.5, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.5, part 5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentRegularity_infiniteLimitNonSubordinator
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ((¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) →
      Tendsto L.ψ atTop atTop) := by
  sorry

end Kyprianou.Ch03
