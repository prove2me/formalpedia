-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0185_0190
-- name    : Freiman.lowerHistory_bindings_0185_0190
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:27.871707+00:00
-- url     : https://prove2.me/theorems/8b233a90-e267-40fd-b6ed-07da078be59a
-- title:
--   Freiman lower-history bindings, indices 185–189
-- statement:
--   For every original catalogue index $i$ with $$185\le i<190$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0180_0190, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 185 190`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0180_0190, UUID 22edb1d6-cbe1-4107-8d4f-35e76063ab49. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 185–189.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0185_0190 : lowerHistoryBindingBatch 185 190 := by sorry
