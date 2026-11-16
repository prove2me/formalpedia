-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_eq_firstUpperPassage_neg
-- name    : Kyprianou.Ch01.firstLowerPassage_eq_firstUpperPassage_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:35:27.82713+00:00
-- url     : https://prove2.me/theorems/94695f5d-0ccc-4aac-b095-3fe3bccbcbd9
-- title:
--   First strict lower passage is first strict upper passage for the sign-reversed path
-- statement:
--   For every real-valued sample path X and barrier a, the strict first passage below −a of X, measured from initial value zero, equals the strict first passage above +a of the path −X. Both stopping-time definitions use positive times and the infimum convention with ∞ for no crossing, so the two sets of admissible times coincide exactly by elementary order algebra. This deterministic identity enables the lower-passage Brownian formula to reuse the already stated upper-passage theorem.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, upper and lower Brownian first-passage transforms.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstLowerPassage_eq_firstUpperPassage_neg
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) :
    (fun ω => Kyprianou.Ch01.firstLowerPassage X 0 (-a) ω) =
      (fun ω => Kyprianou.Ch01.firstUpperPassage
        (fun t ω => -X t ω) a ω) := by sorry
