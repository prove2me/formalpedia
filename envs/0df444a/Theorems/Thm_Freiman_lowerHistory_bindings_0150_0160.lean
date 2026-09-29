-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0150_0160
-- name    : Freiman.lowerHistory_bindings_0150_0160
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:09:56.632523+00:00
-- url     : https://prove2.me/theorems/89d55d60-2d1f-4915-be2e-afa7d4d0bd01
-- title:
--   Freiman lower-history bindings, indices 150–159
-- statement:
--   Let $P_i$ denote the path at index $i$ in the original Freiman lower-history catalogue. For every $i$ in the interval
--
--   $$150\le i<160$$
--
--   the catalogue records for $P_i$ satisfy the complete source-binding and coverage conditions. The recorded number of alternatives agrees with the generated source alternatives; every record is bound to its original premise and witness; the witness rectangle is the path rectangle; and every required alternative is covered.
--
--   This is the indicated subinterval of the existing theorem Freiman.lowerHistory_bindings_0150_0200. All conditions of its original predicate are retained.
--
--   **Formalization Note** The statement is `lowerHistoryBindingBatch 150 160`.
-- source:
--   Exact subinterval restriction of Prove2Me theorem Freiman.lowerHistory_bindings_0150_0200, UUID ac719a39-7484-4bf0-a8a8-3ad44e2c3bc9; original definitions Def_Freiman_lowerHistoryVerification and Def_Freiman_lowerHistoryCatalogL, array indices 150 through 159.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0150_0160 : lowerHistoryBindingBatch 150 160 := by sorry
