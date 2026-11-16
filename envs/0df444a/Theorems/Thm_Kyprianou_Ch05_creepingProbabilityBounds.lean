-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingProbabilityBounds
-- name    : Kyprianou.Ch05.creepingProbabilityBounds
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:52:32.423199+00:00
-- url     : https://prove2.me/theorems/e594e5e0-1c56-4a4b-8869-56c3c35323ee
-- title:
--   Lemma 5.10: initial-limit and square-root creeping bounds
-- statement:
--   If p_x>0 somewhere then sup_{0<eta<epsilon}p_eta tends to 1 as epsilon decreases to zero. If p_x>3/4 then p_y >= 1/2+sqrt(p_x-3/4) for every 0<y<=x.
-- source:
--   Kyprianou (2006), Chapter 5, result 5.10, first edition, printed pp. 119-125.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.10, pp.122-123: two independent quantitative estimates. -/
theorem creepingProbabilityBounds
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
  (((∃ x : Real, 0 < x ∧ 0 < p x) →
     Tendsto
       (fun epsilon : Real =>
         sSup (p '' Set.Ioo (0 : Real) epsilon))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (∀ x : Real, 0 < x → 3 / 4 < p x →
     ∀ y : Real, 0 < y → y ≤ x →
       1 / 2 + Real.sqrt (p x - 3 / 4) ≤ p y))
 := by
  sorry

end Kyprianou.Ch05
