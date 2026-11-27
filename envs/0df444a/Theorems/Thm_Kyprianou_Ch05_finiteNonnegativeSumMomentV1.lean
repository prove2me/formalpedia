-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteNonnegativeSumMomentV1
-- name    : Kyprianou.Ch05.finiteNonnegativeSumMomentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:33:35.311802+00:00
-- url     : https://prove2.me/theorems/28673ab1-946c-494f-bad5-aef8e3406301
-- title:
--   Finite real sum mean identifies nonnegative jump moment
-- statement:
--   Finite real sum mean identifies nonnegative jump moment
-- source:
--   Kyprianou (2006), Theorem 5.7; finite-mean passage and creeping reduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.finiteNonnegativeSumMomentV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → ENNReal) (d : Real) (hd : 0 ≤ d)
    (hfin : ∀ᵐ w ∂P, J w ≠ ⊤)
    (hint : Integrable (fun w => d + (J w).toReal) P) :
    ENNReal.ofReal (∫ w, (d + (J w).toReal) ∂P) =
      ENNReal.ofReal d + ∫⁻ w, J w ∂P := by sorry
