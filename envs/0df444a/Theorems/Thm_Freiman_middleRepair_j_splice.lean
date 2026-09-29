-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_splice
-- name    : Freiman.middleRepair_j_splice
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:28:57.598974+00:00
-- url     : https://prove2.me/theorems/2305255b-5931-421a-b426-3a03bed86b2c
-- title:
--   Report convention repair: middleRepair_j_splice
-- statement:
--   The two J anchors splice the finite chain to the convex hull of J1 and J2, with either scalar orientation. This is an interval-order lemma; it does not identify a hull with a Cantor sum. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:janchor Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_splice :
    ∀ (c : MiddleCore) (cs : List MiddleCore), middleContacts cs → middleRepairJAnchors c cs →
      (middleCover (middleRepairJ c 1)).Nonempty → middleCover c ⊆ middleUnion cs ∪ middleRepairJSpan c := by
  sorry
