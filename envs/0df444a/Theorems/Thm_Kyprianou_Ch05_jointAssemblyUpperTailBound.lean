-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jointAssemblyUpperTailBound
-- name    : Kyprianou.Ch05.jointAssemblyUpperTailBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:16:30.251198+00:00
-- url     : https://prove2.me/theorems/5bc56bcd-4cae-5853-a79a-e19c19ad146f
-- title:
--   Theorem 5.7 (assembly upper): tail of the jump integral vanishes
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, assuming the vanishing-test limit and the creeping limit, for every bounded continuous test $f$ and every $\varepsilon>0$ the window-truncated jump term (outer integral over $y\in[0,x]$) is eventually within $\varepsilon$ below the full jump term: the tail beyond height $x$ is negligible.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.7, printed p. 121, via Corollary 5.3, p. 114.

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
/-- Assembly upper half: truncated jump term within epsilon of the full one. -/
theorem jointAssemblyUpperTailBound
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
    (hVan : ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
     Tendsto (fun x : Real => passageTestExpectation P Y Yleft death x f) atTop
       (nhds ((1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume))))
    (hCreep : Tendsto (fun x : Real => creepingProbability P Y death x) atTop (nhds (d / (∫ omega, Y 1 omega ∂P)))) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) ≤ (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) + ε := by
  sorry
end Kyprianou.Ch05
