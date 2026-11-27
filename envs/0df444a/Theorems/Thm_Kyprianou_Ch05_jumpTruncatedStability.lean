-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jumpTruncatedStability
-- name    : Kyprianou.Ch05.jumpTruncatedStability
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T03:00:52.274242+00:00
-- url     : https://prove2.me/theorems/2deafe1d-8291-4001-a590-6d1298203566
-- title:
--   Theorem 5.7 (stability): truncated jump term is stable in the test, with constant the tail mass over the mean
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, if two bounded continuous tests $f,g$ vanishing at $(0,0)$ differ uniformly by at most $\eta$, then at every level $x$ their window-truncated jump terms differ by at most $\eta$ times the total jump tail mass $\int_0^\infty \Pi((y,\infty))\,dy$ divided by the mean. The estimate is a Tonelli computation: the difference integrand is at most $\eta$ times the tail mass of the jump measure above each starting height, and the window only shrinks the bound.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
/-- Jump-side stability: uniform closeness of tests bounds the truncated jump term difference by eta times the total tail mass over the mean. -/
theorem jumpTruncatedStability
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  ∀ f g : Real × Real → Real, IsBoundedContinuousTest f → IsBoundedContinuousTest g → f (0, 0) = 0 → g (0, 0) = 0 → ∀ η : Real, 0 < η → (∀ z : Real × Real, |f z - g z| ≤ η) → ∀ x : Real, |(1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, g (z - y, y) ∂Pi ∂volume)| ≤ η * ((∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) := by
  sorry
end Kyprianou.Ch05
