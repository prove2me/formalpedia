-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0195_0200
-- name    : Freiman.lowerHistory_bindings_0195_0200
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:32.065779+00:00
-- url     : https://prove2.me/theorems/d8336681-38ca-4dd8-8d03-0e5c51d8bc58
-- title:
--   Freiman lower-history bindings, indices 195–199
-- statement:
--   For every original catalogue index $i$ with $$195\le i<200$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0190_0200, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 195 200`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0190_0200, UUID 216d4629-254d-4208-a312-95748e3c8a11. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 195–199.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0195_0200 : lowerHistoryBindingBatch 195 200 := by sorry
