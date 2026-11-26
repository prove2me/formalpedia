-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteMeanCreepingProbabilityLimit
-- name    : Kyprianou.Ch05.finiteMeanCreepingProbabilityLimit
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-26T03:07:35.306293+00:00
-- url     : https://prove2.me/theorems/7f3e65f1-d570-4f2c-bd35-ea5ae0907c99
-- title:
--   Theorem 5.7 (creeping): limiting creeping probability d/mu
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 (killed subordinator, finite positive mean $\mu$, nonlattice potential), the creeping probability at level $x$ converges as $x\to\infty$ to $d/\mu$, where $d$ is the drift of the Laplace triplet.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121 (creeping conjunct).

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
/-- Theorem 5.7, creeping conjunct: limiting creeping probability. -/
theorem finiteMeanCreepingProbabilityLimit
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
  Tendsto (fun x : Real => creepingProbability P Y death x)
    atTop (nhds (d / (∫ omega, Y 1 omega ∂P))) := by
  sorry
end Kyprianou.Ch05
