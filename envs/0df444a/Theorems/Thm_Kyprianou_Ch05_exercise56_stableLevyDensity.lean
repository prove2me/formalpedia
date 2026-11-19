-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise56_stableLevyDensity
-- name    : Kyprianou.Ch05.exercise56_stableLevyDensity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:41:23.022737+00:00
-- url     : https://prove2.me/theorems/9f45b4df-ac7f-4550-89d7-ff1af8cce6a3
-- title:
--   Exercise 5.6 part 1: Stable Levy-measure density
-- statement:
--   Stable Levy-measure density. Exact original quantified hypotheses and the corresponding mathematical clause of Kyprianou (2006), Chapter 5 Exercise 5.6.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.6, part 1

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.6, all four parts, in the stable regime 0<alpha<1. -/
theorem exercise56_stableLevyDensity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hStablePhi : ∀ theta : Real, 0 ≤ theta → Phi theta = theta ^ alpha)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft) :
  (Pi =
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun z : Real =>
          ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha)))))
 := by
  sorry

end Kyprianou.Ch05
