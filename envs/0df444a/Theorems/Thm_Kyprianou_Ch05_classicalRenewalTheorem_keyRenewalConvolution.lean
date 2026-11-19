-- Prove2me | Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_keyRenewalConvolution
-- name    : Kyprianou.Ch05.classicalRenewalTheorem_keyRenewalConvolution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:40:24.649283+00:00
-- url     : https://prove2.me/theorems/6b6a91b7-f802-4e5a-a670-58a2001d59d8
-- title:
--   Theorem 5.1 part 2: Nonlattice key renewal convolution limit
-- statement:
--   Nonlattice key renewal convolution limit with precisely the original hypotheses and mathematical conclusion of Kyprianou (2006), Theorem 5.1 part 2.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.1, printed pages 112-113, part 2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.1, pp. 112-113, all three renewal conclusions. -/
theorem classicalRenewalTheorem_keyRenewalConvolution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (NonLatticeMeasure F →
      ∀ h : Real → Real, DirectlyRiemannIntegrable h →
        Tendsto
          (fun x : Real =>
            ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
          atTop
          (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu)))
 := by
  sorry

end Kyprianou.Ch05
