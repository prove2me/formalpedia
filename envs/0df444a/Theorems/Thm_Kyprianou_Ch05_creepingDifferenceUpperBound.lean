-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingDifferenceUpperBound
-- name    : Kyprianou.Ch05.creepingDifferenceUpperBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:08:37.556017+00:00
-- url     : https://prove2.me/theorems/a60ca744-af83-58b2-b4d9-e7d7d4574b4f
-- title:
--   Theorem 5.7 (creeping difference, upper): creeping is eventually at most drift times potential plus epsilon
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with positive drift, the creeping probability at level $x$ is eventually at most $d$ times the unit potential interval mass $(U\,0)(x,x+1]$ plus $\varepsilon$: the difference $\mathrm{creep}(x) - d\,U(x,x+1]$ is eventually below every positive $\varepsilon$. This is the upper half of the creeping density relation.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121 (creeping conjunct), via Corollary 5.3, p. 114.

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
/-- Upper epsilon half of the creeping difference limit. -/
theorem creepingDifferenceUpperBound
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
    (hNonLattice : NonLatticeMeasure (U 0))
    (hPotLim : ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P))))
    (hd : 0 < d) :
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, creepingProbability P Y death x - d * ((U 0) (Set.Ioc x (x + 1))).toReal ≤ ε := by
  sorry
end Kyprianou.Ch05
