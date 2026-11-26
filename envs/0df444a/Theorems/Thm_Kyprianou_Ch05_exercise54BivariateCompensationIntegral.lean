-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise54BivariateCompensationIntegral
-- name    : Kyprianou.Ch05.exercise54BivariateCompensationIntegral
-- status  : Open
-- author  : @Cloud 
-- created : 2026-11-26T03:11:45.459097+00:00
-- url     : https://prove2.me/theorems/df1e2368-9004-46c5-918a-8ecd53b87f90
-- title:
--   Exercise 5.4 core: passage probability as compensated U-Pi double integral
-- statement:
--   Under the hypotheses of Exercise 5.4 (possibly correlated killed bivariate subordinator, $U$ its exact bivariate killed potential, $X_{\tau-},Y_{\tau-}$ left-limit versions at the first strict passage time $\tau$ of $Y$ over $x>0$), the probability of the quadruple passage event $\{\tau<\infty,\ \Delta X_\tau\in T,\ X_{\tau-}\in S,\ x-Y_{\tau-}\in B,\ Y_\tau-x\in A\}$ equals the compensated double integral $$\int U(d\mathrm{pre})\int \Pi(d\mathrm{jump})\ \mathbf 1[\mathrm{jump}_1\in T,\ \mathrm{pre}_1\in S,\ x-\mathrm{pre}_2\in B,\ \mathrm{pre}_2+\mathrm{jump}_2-x\in A,\ \mathrm{pre}_2\le x<\mathrm{pre}_2+\mathrm{jump}_2].$$ This is the analytic heart of Exercise 5.4 with the kernel definition left unfolded; folding the definition back gives the quadruple law.
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

attribute [instance] Classical.propDecidable

namespace Kyprianou.Ch05

/-- Core of Exercise 5.4: the passage event's probability equals the
compensated double integral over the bivariate potential U and the joint
jump measure Pi, before the kernel definition is folded back in. -/
theorem exercise54BivariateCompensationIntegral
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
       ∫⁻ pre : Real × Real,
    ∫⁻ jump : Real × Real,
      (if jump.1 ∈ T ∧ pre.1 ∈ S ∧
        x-pre.2 ∈ B ∧ pre.2+jump.2-x ∈ A ∧
        pre.2 ≤ x ∧ x < pre.2+jump.2
       then (1 : ENNReal) else 0) ∂Pi ∂U
 := by
  sorry

end Kyprianou.Ch05
