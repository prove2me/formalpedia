-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CompletedNaturalCongrV1
-- name    : Kyprianou.Ch04.exercise45CompletedNaturalCongrV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:16:26.486259+00:00
-- url     : https://prove2.me/theorems/726b12aa-53d2-5c17-b1df-6e6027826cf6
-- title:
--   Completed natural filtration is invariant under almost-sure versions
-- statement:
--   Two real processes with a.e. equal time sections have the same completed natural filtration.
-- source:
--   Kyprianou Exercise 4.5, version normalisation

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Completed natural filtrations are unchanged by a pointwise almost-sure modification. -/
theorem Kyprianou.Ch04.exercise45CompletedNaturalCongrV1 {Ω : Type} [m : MeasurableSpace Ω] (P : Measure Ω)
    (X Y : NNReal → Ω → ℝ) (F : Filtration NNReal m)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hEq : ∀ t, X t =ᵐ[P] Y t) :
    Kyprianou.Ch03.IsCompletedNaturalFiltration P Y F := by
  sorry
