-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise54PredictableCompensationAtPassage
-- name    : Kyprianou.Ch05.exercise54PredictableCompensationAtPassage
-- status  : Open
-- author  : @Cloud 
-- created : 2026-11-26T03:11:47.737877+00:00
-- url     : https://prove2.me/theorems/f53a7d52-8d24-40aa-9aee-8b16e95c7101
-- title:
--   Exercise 5.4: predictable compensation at the first passage jump
-- statement:
--   Bivariate jump compensation evaluated at the first passage jump: for every nonnegative measurable integrand $F(\mathrm{pre},\mathrm{jump})$, the expectation over paths of $F$ evaluated at the pre-jump position $(X_{\tau-},Y_{\tau-})$ and the passage jump $(\Delta X_\tau,\Delta Y_\tau)$, restricted to finite passage with $Y_{\tau-}\le x<Y_\tau$, equals $$\int U(d\mathrm{pre})\int \Pi(d\mathrm{jump})\ \mathbf 1[\mathrm{pre}_2\le x<\mathrm{pre}_2+\mathrm{jump}_2]\ F(\mathrm{pre},\mathrm{jump}),$$ where $U$ is the exact bivariate killed potential. This is the Ikeda--Watanabe / compensation-formula step of Exercise 5.4, with $U$ arising as the occupation (predictable projection) measure of the bivariate path before death.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.4, pp.134-135 and worked solution on p.324; Ikeda-Watanabe compensation formula for Levy jump measures.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

attribute [instance] Classical.propDecidable

namespace Kyprianou.Ch05


theorem exercise54PredictableCompensationAtPassage
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
  ∀ (F : (Real × Real) → (Real × Real) → ENNReal),
    Measurable (fun p : (Real × Real) × (Real × Real) => F p.1 p.2) →
    ∀ x : Real, 0 < x →
    (∫⁻ omega : Omega,
      (if PassageFinite Y death x omega ∧
          Yleft (passageFiniteTime Y death x omega) omega ≤ x ∧
          x < Y (passageFiniteTime Y death x omega) omega
       then F (Xleft (passageFiniteTime Y death x omega) omega,
                Yleft (passageFiniteTime Y death x omega) omega)
              (X (passageFiniteTime Y death x omega) omega -
                Xleft (passageFiniteTime Y death x omega) omega,
               Y (passageFiniteTime Y death x omega) omega -
                Yleft (passageFiniteTime Y death x omega) omega)
       else 0) ∂P) =
    ∫⁻ pre : Real × Real,
      ∫⁻ jump : Real × Real,
        (if pre.2 ≤ x ∧ x < pre.2 + jump.2
         then F pre jump else 0) ∂Pi ∂U
 := by
  sorry

end Kyprianou.Ch05
