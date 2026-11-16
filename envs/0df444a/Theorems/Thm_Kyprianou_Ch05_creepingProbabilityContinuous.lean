-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingProbabilityContinuous
-- name    : Kyprianou.Ch05.creepingProbabilityContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:52:54.286703+00:00
-- url     : https://prove2.me/theorems/1d8d7c86-5778-4bac-ba26-b72934ba78c9
-- title:
--   Lemma 5.11: positive and continuous creeping probabilities
-- statement:
--   If p_x>0 at one positive level, p_epsilon tends to one as epsilon->0+ and p is strictly positive and continuous on [0,infinity).
-- source:
--   Kyprianou (2006), Chapter 5, result 5.11, first edition, printed pp. 119-125.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.11, p.124: positive creeping propagates, with zero endpoint
limit equal to one and continuity on the closed nonnegative halfline. -/
theorem creepingProbabilityContinuous
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤)
 :
  let p := creepingProbability P Y death
  ((∃ x : Real, 0 < x ∧ 0 < p x) →
     (Tendsto p (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
     ContinuousOn p (Set.Ici (0 : Real)) ∧
     (∀ x : Real, 0 ≤ x → 0 < p x))
 := by
  sorry

end Kyprianou.Ch05
