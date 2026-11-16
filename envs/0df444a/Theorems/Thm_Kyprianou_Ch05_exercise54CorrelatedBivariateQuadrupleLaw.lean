-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise54CorrelatedBivariateQuadrupleLaw
-- name    : Kyprianou.Ch05.exercise54CorrelatedBivariateQuadrupleLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:57:16.009871+00:00
-- url     : https://prove2.me/theorems/e1347870-bda0-4588-8d92-4fa874311513
-- title:
--   Exercise 5.4: four-variable law for possibly correlated killed subordinators
-- statement:
--   Complete four-coordinate passage law: Delta X_tau, X_tau-, x-Y_tau-, Y_tau-x, with joint renewal U(ds,x-dy) and joint jump Pi(dt,du+y), unrestricted X/Y correlation, killing and all measurable rectangle endpoints. Source labels tau as first passage of X, but its own formula forces crossed coordinate Y; this correction is recorded for independent owner audit and may require source clarification.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.4, pp.134-135 and worked solution on p.324.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.4: full quadruple joint law, with possibly correlated
bivariate subordinators. The second process Y crosses level x, as the
printed U(ds,x-dy) Pi(dt,du+y) kernel requires; the source's tau_X
label is inconsistent with its own formula and is flagged for review. -/
theorem exercise54CorrelatedBivariateQuadrupleLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y Xleft Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta dX dY : Real)
    (Pi U : Measure (Real × Real))
    (hBivariate : IsKilledBivariateSubordinator P X Y death eta dX dY Pi)
    (hPotential : IsBivariateKilledPotential P X Y death U)
    (hLeftX : IsLeftLimitVersion P X Xleft)
    (hLeftY : IsLeftLimitVersion P Y Yleft) :
  ∀ x : Real, 0 < x →
    ∀ T S B A : Set Real,
      MeasurableSet T → MeasurableSet S →
      MeasurableSet B → MeasurableSet A →
      T ⊆ Set.Ici (0 : Real) → S ⊆ Set.Ici (0 : Real) →
      B ⊆ Set.Icc (0 : Real) x → A ⊆ Set.Ioi (0 : Real) →
      P {omega : Omega |
        PassageFinite Y death x omega ∧
        (X (passageFiniteTime Y death x omega) omega -
          Xleft (passageFiniteTime Y death x omega) omega) ∈ T ∧
        Xleft (passageFiniteTime Y death x omega) omega ∈ S ∧
        (x - Yleft (passageFiniteTime Y death x omega) omega) ∈ B ∧
        (Y (passageFiniteTime Y death x omega) omega-x) ∈ A} =
       bivariateQuadrupleKernel U Pi x T S B A
 := by
  sorry

end Kyprianou.Ch05
