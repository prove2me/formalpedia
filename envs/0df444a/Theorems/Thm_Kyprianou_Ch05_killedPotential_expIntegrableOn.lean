-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_expIntegrableOn
-- name    : Kyprianou.Ch05.killedPotential_expIntegrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:12:26.13021+00:00
-- url     : https://prove2.me/theorems/3d284719-9994-4bac-8f56-a57ae34f3fa4
-- title:
--   Finite Laplace resolvent implies integrability on every measurable set
-- statement:
--   The total potential Laplace lintegral is finite; the restricted integral is bounded by it.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); Chapter 1 and Chapter 3 reuse.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical

theorem Kyprianou.Ch05.killedPotential_expIntegrableOn
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (alpha beta : Real) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hpos : 0 < alpha + Phi beta) (B : Set Real) :
    IntegrableOn (fun z : Real => Real.exp (-beta*z)) B (U alpha) := by
  sorry
