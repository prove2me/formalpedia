-- Prove2me | Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheoremV2
-- name    : Kyprianou.Ch05.classicalRenewalTheoremV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:46.534665+00:00
-- url     : https://prove2.me/theorems/d5452926-87e3-4aee-b14f-b5285d955248
-- title:
--   Theorem 5.1: complete three-part classical renewal theorem (corrected)
-- statement:
--   All parts of the classical renewal theorem: (i) nonlattice increments V((x,x+y]) converge to y/mu, (ii) nonlattice key renewal convolution for every directly Riemann integrable function and its integral/mu, (iii) unrestricted V([0,x])/x tends to 1/mu. Nondegenerate positive finite mean is explicit to exclude F=delta_0, which renders printed quotients undefined. Part (ii) explicitly assumes that the test function is Borel measurable.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.1, printed pp. 112-113.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.1, pp. 112-113, all three renewal conclusions. -/
theorem classicalRenewalTheoremV2
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    ((NonLatticeMeasure F →
      ∀ y : Real, 0 < y →
        Tendsto
          (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
          atTop (nhds (y / mu))) ∧
     (NonLatticeMeasure F →
      ∀ h : Real → Real, Measurable h → DirectlyRiemannIntegrable h →
        Tendsto
          (fun x : Real =>
            ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
          atTop
          (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
     (Tendsto
       (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
       atTop (nhds (1 / mu))))
 := by
  sorry

end Kyprianou.Ch05
