-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingZeroDriftEventualBound
-- name    : Kyprianou.Ch05.creepingZeroDriftEventualBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T01:47:20.852511+00:00
-- url     : https://prove2.me/theorems/7726de51-b31d-5a56-ae4a-b0133398239e
-- title:
--   Theorem 5.7 (creeping, zero drift): creeping probability eventually below every epsilon
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7 with zero drift $d=0$, for every $\varepsilon>0$ the creeping probability at level $x$ is eventually at most $\varepsilon$. With no drift there is no continuous crossing, so creeping means a jump lands exactly on the level; under the nonlattice hypothesis this exact-landing probability is asymptotically negligible. Since the creeping probability is nonnegative, this single eventual bound is the whole content of its convergence to $0$.
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
/-- Zero drift: the creeping probability is eventually below every epsilon. -/
theorem creepingZeroDriftEventualBound
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
    (hd : d = 0) :
  ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, creepingProbability P Y death x ≤ ε := by
  sorry
end Kyprianou.Ch05
