-- Prove2me | Theorems.Thm_Kyprianou_Ch05_vanishingUpperTailBound
-- name    : Kyprianou.Ch05.vanishingUpperTailBound
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:16:34.430822+00:00
-- url     : https://prove2.me/theorems/ee44c50d-c3fb-4630-90e8-a73a2c623a74
-- title:
--   Theorem 5.7 (vanishing upper): tail of the jump integral vanishes
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, for every bounded continuous test $f$ vanishing at $(0,0)$ and every $\varepsilon>0$, the window-truncated jump term (outer integral over $y\in[0,x]$) is eventually within $\varepsilon$ below the full jump term: the tail of the jump integral beyond height $x$ is negligible. This is the tail-integrability half of the vanishing-test step.
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
/-- Upper half: window-truncated jump integral approaches the full one from within epsilon. -/
theorem vanishingUpperTailBound
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) ≤ (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) + ε := by
  sorry
end Kyprianou.Ch05
