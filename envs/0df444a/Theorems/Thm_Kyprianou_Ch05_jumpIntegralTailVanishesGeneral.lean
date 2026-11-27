-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jumpIntegralTailVanishesGeneral
-- name    : Kyprianou.Ch05.jumpIntegralTailVanishesGeneral
-- status  : Open
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:37:06.333087+00:00
-- url     : https://prove2.me/theorems/3a6e18b3-a2bd-5aec-b925-1c2504509626
-- title:
--   Theorem 5.7 (jump integral, general tests): the tail beyond height x vanishes in absolute value
-- statement:
--   Under the hypotheses of Kyprianou Theorem 5.7, for every bounded continuous test $f$ (no vanishing condition at the origin) and every $\varepsilon>0$, the difference between the full jump term and its window truncation (outer integral over starting heights $y\in[0,x]$) is eventually at most $\varepsilon$ in absolute value. The tail is integrable for general tests because finite mean gives $\int z\,\Pi(dz)<\infty$ for the jump measure of the subordinator.
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
/-- Jump integral tail, general tests: truncated and full jump terms differ by at most epsilon eventually. -/
theorem jumpIntegralTailVanishesGeneral
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
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop, |(1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Ici (0 : Real), ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  sorry
end Kyprianou.Ch05
