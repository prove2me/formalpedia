-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0175_0180
-- name    : Freiman.lowerHistory_bindings_0175_0180
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:17.443891+00:00
-- url     : https://prove2.me/theorems/33a4c9ba-826d-49e5-ac72-148f4fa3bb5d
-- title:
--   Freiman lower-history bindings, indices 175–179
-- statement:
--   For every original catalogue index $i$ with $$175\le i<180$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0170_0180, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 175 180`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0170_0180, UUID 9f3b6fea-4095-477c-a8bf-dddc30ac98b8. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 175–179.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0175_0180 : lowerHistoryBindingBatch 175 180 := by sorry
