-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialRenewalIdentity
-- name    : Kyprianou.Ch05.potentialRenewalIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:48:10.234719+00:00
-- url     : https://prove2.me/theorems/236fd4ab-a605-4b79-a83b-a3aaf7704a5b
-- title:
--   Lemma 5.2: undiscounted potential equals renewal minus delta zero
-- statement:
--   For an unkilled subordinator, F=U^(1) and V=sum F^{*k}; the full measure identity V=delta_0+U^(0), including its origin atom, holds.
-- source:
--   Kyprianou (2006), first edition, numbered result 5.2, Section 5.1, printed pp. 113-115.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.2, p. 113: U^(1) renewal measure is delta_0+U. -/
theorem potentialRenewalIdentity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0
 := by
  sorry

end Kyprianou.Ch05
