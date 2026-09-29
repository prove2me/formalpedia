-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0170_0175
-- name    : Freiman.lowerHistory_bindings_0170_0175
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:09.430748+00:00
-- url     : https://prove2.me/theorems/d5f4680e-fc28-4167-bf51-ad014c4a31c5
-- title:
--   Freiman lower-history bindings, indices 170–174
-- statement:
--   For every original catalogue index $i$ with $$170\le i<175$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0170_0180, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 170 175`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0170_0180, UUID 9f3b6fea-4095-477c-a8bf-dddc30ac98b8. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 170–174.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0170_0175 : lowerHistoryBindingBatch 170 175 := by sorry
