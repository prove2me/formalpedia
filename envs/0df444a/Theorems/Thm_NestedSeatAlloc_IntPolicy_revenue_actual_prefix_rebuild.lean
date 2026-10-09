-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_actual_prefix_rebuild
-- name    : NestedSeatAlloc.IntPolicy.revenue_actual_prefix_rebuild
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:21:11.347389+00:00
-- url     : https://prove2.me/theorems/cf8e8faf-03ba-4f93-8fbf-5d7da5294061
-- title:
--   Actual nested revenue factors through the next-class demand and the finite higher-fare prefix
-- statement:
--   # Actual nested revenue depends only on the next demand and prefix
--
--   The preceding frozen-prefix lemma relates revenue after replacing the
--   demand at index k+1 with an arbitrary value y to revenue reconstructed
--   from the high-fare prefix and y. Choose y=X(k+1)(ω).
--   Mathlib's Function.update_eq_self establishes that updating a
--   function at an index with its existing value changes nothing.
--
--   The equality follows immediately with the accepted
--   revenue_frozen_prefix_rebuild theorem and one simplification. This
--   proves that the actual nested revenue through k+1 classes factors
--   through the measurable pair (X(k+1), U), where U is the prefix
--   vector over Finset.Icc 1 k.
--
--   The identity is the key factorisation used with integrable_map_measure
--   to transfer the known integrability of actual revenue (proved by
--   revenue_integrable_of_seat_model) to the product marginal measure.
--   Remote Lean compilation is authoritative; no local Lean is run.
-- source:
--   # Actual nested revenue depends only on the next demand and prefix
--
--   The preceding frozen-prefix lemma relates revenue after replacing the
--   demand at index k+1 with an arbitrary value y to revenue reconstructed
--   from the high-fare prefix and y. Choose y=X(k+1)(ω).
--   Mathlib's Function.update_eq_self establishes that updating a
--   function at an index with its existing value changes nothing.
--
--   The equality follows immediately with the accepted
--   revenue_frozen_prefix_rebuild theorem and one simplification. This
--   proves that the actual nested revenue through k+1 classes factors
--   through the measurable pair (X(k+1), U), where U is the prefix
--   vector over Finset.Icc 1 k.
--
--   The identity is the key factorisation used with integrable_map_measure
--   to transfer the known integrability of actual revenue (proved by
--   revenue_integrable_of_seat_model) to the product marginal measure.
--   Remote Lean compilation is authoritative; no local Lean is run.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.revenue_actual_prefix_rebuild {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (ω : Ω) (s : ℝ) :
    revenue f p (fun i => X i ω) (k + 1) s =
    revenue f p (prefixRevenueRebuild k
      (X (k + 1) ω, fun i : (Finset.Icc 1 k) => X i.1 ω))
      (k + 1) s := by sorry
