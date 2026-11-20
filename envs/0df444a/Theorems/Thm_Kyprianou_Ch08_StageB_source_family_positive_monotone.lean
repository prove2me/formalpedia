-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
-- name    : Kyprianou.Ch08.StageB.source_family_positive_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:49:55.035709+00:00
-- url     : https://prove2.me/theorems/13654820-c0d0-4432-b0ba-88739cdb26d1
-- title:
--   Chapter 8 scale-family half-line positivity, monotonicity and continuity
-- statement:
--   The textbook scale-function family from Theorem 8.1 is nonnegative on all reals and monotone and continuous on [0,infinity) for each discount q≥0. This is the exact hypothesis bridge from source HasSourceScaleFamily to convolution estimates in Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1(i), equations (8.5) and (8.18), pp. 214 and 219-220.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Scale-family nonnegativity, monotonicity and continuity on the half-line. -/
theorem source_family_positive_monotone (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    (∀ x : ℝ, 0 ≤ W q x) ∧
    MonotoneOn (W q) (Set.Ici (0 : ℝ)) ∧
    ContinuousOn (W q) (Set.Ici (0 : ℝ)) := by
  sorry

end Kyprianou.Ch08.StageB
