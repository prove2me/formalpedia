-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorPotentialRenewalLimits
-- name    : Kyprianou.Ch05.subordinatorPotentialRenewalLimits
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:48:55.281732+00:00
-- url     : https://prove2.me/theorems/fcb23456-1e1f-487b-828b-a95cacc96d37
-- title:
--   Corollary 5.3: two potential-measure renewal asymptotics
-- statement:
--   An unkilled subordinator of finite positive mean mu has U((x,x+y]) tending to y/mu under nonlattice support, and U([0,x])/x tending to 1/mu without restriction on lattice support.
-- source:
--   Kyprianou (2006), first edition, numbered result 5.3, Section 5.1, printed pp. 113-115.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Corollary 5.3, p. 114: no-lattice local increments and global growth. -/
theorem subordinatorPotentialRenewalLimits
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P) :
  let mu : Real := ∫ omega, Y 1 omega ∂P
  ((NonLatticeMeasure (U 0) →
    ∀ y : Real, 0 < y →
      Tendsto
        (fun x : Real =>
          ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / mu))) ∧
   (Tendsto
     (fun x : Real =>
       ((U 0) (Set.Icc (0 : Real) x)).toReal / x)
     atTop (nhds (1 / mu))))
 := by
  sorry

end Kyprianou.Ch05
