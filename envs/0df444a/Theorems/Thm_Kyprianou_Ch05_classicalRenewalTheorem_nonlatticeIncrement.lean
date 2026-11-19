-- Prove2me | Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_nonlatticeIncrement
-- name    : Kyprianou.Ch05.classicalRenewalTheorem_nonlatticeIncrement
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:40:28.564285+00:00
-- url     : https://prove2.me/theorems/b176b15b-454a-4ba5-acbe-94ebda0502ec
-- title:
--   Theorem 5.1 part 1: Nonlattice local renewal increment limit
-- statement:
--   Nonlattice local renewal increment limit with precisely the original hypotheses and mathematical conclusion of Kyprianou (2006), Theorem 5.1 part 1.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.1, printed pages 112-113, part 1

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.1, pp. 112-113, all three renewal conclusions. -/
theorem classicalRenewalTheorem_nonlatticeIncrement
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (NonLatticeMeasure F →
      ∀ y : Real, 0 < y →
        Tendsto
          (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
          atTop (nhds (y / mu)))
 := by
  sorry

end Kyprianou.Ch05
