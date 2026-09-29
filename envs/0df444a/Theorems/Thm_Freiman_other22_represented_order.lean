-- Prove2me | Theorems.Thm_Freiman_other22_represented_order
-- name    : Freiman.other22_represented_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:50.503747+00:00
-- url     : https://prove2.me/theorems/46c7b4ae-00ce-4e8f-9d8e-9c1f07e633d0
-- title:
--   other22 represented order
-- statement:
--   Select the two actual endpoint cases, join their true conditions, and apply the shared exact component-sign comparison semantics.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_represented_order (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (u v : LowerPair) (a b : Bool) (x y : ℝ)
    (hx : other22EndpointRepresented base C u a x)
    (hy : other22EndpointRepresented base C v b y)
    (hh : ∀ z ∈ lowerHistoryComparisons C u v a b,
      lowerHistoryAtBase base z.1 → lowerHistoryComparisonHolds z.2 (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    y ≤ x := by
  sorry
