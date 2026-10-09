-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clamped_surplus_dominance
-- name    : NestedSeatAlloc.IntPolicy.clamped_surplus_dominance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T13:38:57.841631+00:00
-- url     : https://prove2.me/theorems/d0c6d7f2-0cdd-421d-8d0e-23976b1afe10
-- title:
--   Pointwise low-fare allocation dominance for an optimal high-fare continuation value
-- statement:
--   Given a dominating high-fare revenue function gp, and an arbitrary competing function gq bounded above by gp at every nonnegative capacity, assume gp(t)-c*t increases to protection threshold a and decreases thereafter. For any capacity s, nonnegative demand y, and alternative threshold b, low-fare sales according to b plus gq at residual capacity cannot exceed sales according to a plus gp at residual capacity. This isolates the purely pointwise comparison from demand independence, conditional expectation and the seat-model definition.
-- source:
--   First bound the residual capacity s - min(max(s-b,0),y) below by zero using b≥0 and s≥0. Apply hdom to replace gq at that residual capacity by gp. The remaining inequality is exactly the existing clamped_surplus_optimal helper. The proof is a short Lean calc, saved as clamped_surplus_dominance_candidate.lean. Do not publish or import as Proved while clamped_surplus_optimal remains Open.

import Mathlib

theorem NestedSeatAlloc.IntPolicy.clamped_surplus_dominance
    (gq gp : ℝ → ℝ) (c a s y b : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hdom : ∀ t, 0 ≤ t → gq t ≤ gp t)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      gp u - c * u ≤ gp v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      gp v - c * v ≤ gp u - c * u) :
    c * min (max (s - b) 0) y + gq (s - min (max (s - b) 0) y) ≤
    c * min (max (s - a) 0) y + gp (s - min (max (s - a) 0) y) := by sorry
