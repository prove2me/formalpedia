-- Prove2me | Theorems.Thm_HardyFLocal_product_tests_span
-- name    : HardyFLocal.product_tests_span
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:07:19.770584+00:00
-- url     : https://prove2.me/theorems/069fb9e9-b1d3-466c-837f-b5a79204a988
-- title:
--   Physical product tests span all joint clump coordinates
-- statement:
--   If the single-component test columns are linearly independent, and physical states realize every product of tests across finitely many components, those physical coordinate vectors span the entire joint coordinate space. This includes an empty collection of components.
-- source:
--   Algebraic step for Hardy, arXiv:0804.0054, section 5, interior clump fiducial minimality.

import Mathlib
open Classical

namespace HardyFLocal

open Classical in
theorem product_tests_span {D K T R : Type} [Fintype D] [Fintype K] [Fintype T]
    (w : K → T → ℝ) (hw : LinearIndependent ℝ w) (state : R → (D → K) → ℝ)
    (realize : ∀ t : D → T, ∃ s : R, ∀ k, state s k = ∏ d, w (k d) (t d)) :
    Submodule.span ℝ (Set.range state) = ⊤ := by sorry

end HardyFLocal
