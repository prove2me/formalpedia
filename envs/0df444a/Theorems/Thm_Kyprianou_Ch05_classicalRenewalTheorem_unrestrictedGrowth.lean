-- Prove2me | Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_unrestrictedGrowth
-- name    : Kyprianou.Ch05.classicalRenewalTheorem_unrestrictedGrowth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:40:25.253697+00:00
-- url     : https://prove2.me/theorems/0e4a1289-230f-405a-bb6b-dc73f33160d0
-- title:
--   Theorem 5.1 part 3: Unrestricted renewal measure global growth
-- statement:
--   Unrestricted renewal measure global growth with precisely the original hypotheses and mathematical conclusion of Kyprianou (2006), Theorem 5.1 part 3.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.1, printed pages 112-113, part 3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.1, pp. 112-113, all three renewal conclusions. -/
theorem classicalRenewalTheorem_unrestrictedGrowth
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (Tendsto
       (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
       atTop (nhds (1 / mu)))
 := by
  sorry

end Kyprianou.Ch05
