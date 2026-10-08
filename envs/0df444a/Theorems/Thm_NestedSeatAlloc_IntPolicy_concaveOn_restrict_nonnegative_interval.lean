-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_concaveOn_restrict_nonnegative_interval
-- name    : NestedSeatAlloc.IntPolicy.concaveOn_restrict_nonnegative_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:32:30.203587+00:00
-- url     : https://prove2.me/theorems/4a8f4421-31f7-4ebc-a047-e12e1bfb63d4
-- title:
--   Restrict nonnegative concavity to an interval
-- statement:
--   A function concave on the nonnegative ray remains concave on any interval whose left endpoint is nonnegative.
-- source:
--   Complete restriction helper for the left region of the conditional-revenue three-piece concavity proof.

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem concaveOn_restrict_nonnegative_interval {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Icc a b) g := by sorry

end NestedSeatAlloc.IntPolicy
