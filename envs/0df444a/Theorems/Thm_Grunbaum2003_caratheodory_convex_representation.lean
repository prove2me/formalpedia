-- Prove2me | Theorems.Thm_Grunbaum2003_caratheodory_convex_representation
-- name    : Grunbaum2003.caratheodory_convex_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T02:54:31.802303+00:00
-- url     : https://prove2.me/theorems/22ecc090-90ac-4db4-99ef-58288b2ce96e
-- title:
--   Theorem 2.3.5 — Carathéodory convex representation
-- statement:
--   For any A ⊆ ℝ^d and every x ∈ conv A, there are d+1 points x_i ∈ A and nonnegative real weights α_i summing to 1 such that x = ∑ᵢ α_i x_i. Repetitions and zero weights are allowed.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §2.3, Theorem 2.3.5, printed p. 15 / source.pdf p. 33; PDF SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Grünbaum (2003), §2.3, Theorem 5 (2.3.5), printed p. 15 / PDF p. 33.
Every point in the convex hull of an arbitrary subset of real d-space is
represented using d+1 points of that subset. Repetitions and zero weights
are allowed, exactly as in the source. Statement-only local staging.
Mathlib's `convexHull_eq_union` gives the compatible affine-independent
finite-support formulation; no new convex-hull adapter is introduced. -/
theorem caratheodory_convex_representation (d : ℕ)
    (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ A) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ x = ∑ i, w i • v i := by sorry

end Grunbaum2003
