-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise51ProveTheorem57
-- name    : Kyprianou.Ch05.exercise51ProveTheorem57
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:55:35.892545+00:00
-- url     : https://prove2.me/theorems/66d19c10-bf90-44a1-bab6-eb9d32a46272
-- title:
--   Exercise 5.1: independent proof of the complete Theorem 5.7
-- statement:
--   Prove the full finite-mean nonlattice joint overshoot and undershoot weak limit, including the mass d/mu at creeping and the separate limiting creeping probability. The proof must reconstruct Theorem 5.7 from Corollary 5.3 and Lemma 5.5 without importing or assuming the Open Theorem 5.7.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.1, printed p. 133, worked solution p. 322, and theorem 5.7 printed p. 121.

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

/-- Theorem 5.7, p.121: entire finite-mean weak joint law,
including the creeping mass d/mu at (0,0), and its separate limit. -/
theorem exercise51ProveTheorem57
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
  let mu : Real := ∫ omega, Y 1 omega ∂P
  ((∀ f : Real × Real → Real, IsBoundedContinuousTest f →
     Tendsto
       (fun x : Real => passageTestExpectation P Y Yleft death x f)
       atTop
       (nhds
         (d / mu * f (0,0) +
           (1 / mu) *
             (∫ y in Set.Ici (0 : Real),
                ∫ z in Set.Ioi y, f (z-y,y) ∂Pi ∂volume)))) ∧
   (Tendsto (fun x : Real => creepingProbability P Y death x)
     atTop (nhds (d / mu))))
 := by
  sorry

end Kyprianou.Ch05
