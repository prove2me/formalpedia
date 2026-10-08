-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_policy_agree_below
-- name    : NestedSeatAlloc.IntPolicy.revenue_policy_agree_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T02:20:36.426674+00:00
-- url     : https://prove2.me/theorems/220c957e-00cd-470b-bb75-03c75ba67b7a
-- title:
--   Finite-prefix revenue depends only on earlier protection coordinates
-- statement:
--   For every finite revenue prefix k, two protection policies that agree at all coordinates below k produce the same revenue at every seat count.
-- source:
--   This is a direct invariant of the authoritative nested-seat recursion in Definitions.Def_NestedSeatAlloc_IntPolicy_Model: revenue at level k reads only protection coordinates strictly below k. It is a source-faithful lemma for theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739), isolating the exact fact that varying q_j first affects level j+1. The lemma does not assert a parent-child graph edge or close the parent theorem.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.revenue_policy_agree_below (f p q x : ℕ → ℝ) : ∀ k, (∀ i, 1 ≤ i → i < k → p i = q i) → ∀ s, revenue f p x k s = revenue f q x k s := by sorry
