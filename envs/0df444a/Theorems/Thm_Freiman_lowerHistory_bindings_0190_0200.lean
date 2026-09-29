-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0190_0200
-- name    : Freiman.lowerHistory_bindings_0190_0200
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:10:25.465718+00:00
-- url     : https://prove2.me/theorems/216d4629-254d-4208-a312-95748e3c8a11
-- title:
--   Freiman lower-history bindings, indices 190–199
-- statement:
--   Let $P_i$ denote the path at index $i$ in the original Freiman lower-history catalogue. For every $i$ in the interval
--
--   $$190\le i<200$$
--
--   the catalogue records for $P_i$ satisfy the complete source-binding and coverage conditions. The recorded number of alternatives agrees with the generated source alternatives; every record is bound to its original premise and witness; the witness rectangle is the path rectangle; and every required alternative is covered.
--
--   This is the indicated subinterval of the existing theorem Freiman.lowerHistory_bindings_0150_0200. All conditions of its original predicate are retained.
--
--   **Formalization Note** The statement is `lowerHistoryBindingBatch 190 200`.
-- source:
--   Exact subinterval restriction of Prove2Me theorem Freiman.lowerHistory_bindings_0150_0200, UUID ac719a39-7484-4bf0-a8a8-3ad44e2c3bc9; original definitions Def_Freiman_lowerHistoryVerification and Def_Freiman_lowerHistoryCatalogL, array indices 190 through 199.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0190_0200 : lowerHistoryBindingBatch 190 200 := by sorry
