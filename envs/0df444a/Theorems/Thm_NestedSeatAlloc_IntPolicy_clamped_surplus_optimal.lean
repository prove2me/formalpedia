-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clamped_surplus_optimal
-- name    : NestedSeatAlloc.IntPolicy.clamped_surplus_optimal
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T12:07:16.468348+00:00
-- url     : https://prove2.me/theorems/0523c9b6-35ef-4852-84f7-6b53882da0fc
-- title:
--   Pointwise optimality of the clamped low-fare allocation under unimodal adjusted high-fare revenue
-- statement:
--   # Pointwise optimality of the protection-level clamp
--
--   Let g(t) be the optimal expected revenue available to the high-fare nest with t seats, let c be the next fare, a be the proposed protection level and b an alternative protection level. With capacity s and realised low-fare demand y, the sales under threshold z are U(z) = min(max(s-z,0), y). The resulting conditional total revenue is c U(z) + g(s-U(z)).
--
--   Assume g(t)-c*t is non-decreasing on [0,a] and non-increasing on [a,infinity). The clamped allocation a maximises c U(z)+g(s-U(z)) among every non-negative z, because the remaining high-fare seats t=s-U(z) lie within [max(0,s-y),s] and the choice z=a yields the point in this interval closest to a.
--
--   The Lean proof explicitly splits into a>=s (zero low-fare sales), a<=s-y (all demand sold), and s-y<a<s (the threshold itself is feasible), and applies the left/right unimodality inequalities. All seat and demand bounds are kept explicit.
--
--   This is a pointwise deterministic optimisation bridge for the revised all-seat optimality step. It does not claim that the corresponding monotonicity hypotheses follow from InSubdiff for an arbitrary function. The remaining analytic task is to derive them from concavity of the high-fare revenue and the subdifferential condition, and then integrate against the realised demand. The lemma provides genuine proof content rather than an unused import solely for graph layout.
-- source:
--   Pointwise optimisation of low-fare sales U(z)=min(max(s-z,0),y): the proposed threshold a maximises c U(z)+g(s-U(z)) whenever t ↦ g(t)-c*t increases up to a and decreases thereafter, for nonnegative capacity, demand and thresholds. The proof is by three cases on the position of a relative to [s-y,s]. This lemma isolates the algebraic layer of the strengthened Theorem 1 optimality step without presupposing concavity or attempting to link the derivative milestones artificially.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

theorem NestedSeatAlloc.IntPolicy.clamped_surplus_optimal (g : ℝ → ℝ) (c a s y b : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      g u - c * u ≤ g v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      g v - c * v ≤ g u - c * u) :
    c * min (max (s - b) 0) y + g (s - min (max (s - b) 0) y) ≤
    c * min (max (s - a) 0) y + g (s - min (max (s - a) 0) y) := by sorry
