-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0190_0195
-- name    : Freiman.lowerHistory_bindings_0190_0195
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:01.009418+00:00
-- url     : https://prove2.me/theorems/afaae5bb-bafc-402d-9273-5bc6f2eb3891
-- title:
--   Freiman lower-history bindings, indices 190–194
-- statement:
--   For every original catalogue index $i$ with $$190\le i<195$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0190_0200, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 190 195`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0190_0200, UUID 216d4629-254d-4208-a312-95748e3c8a11. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 190–194.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0190_0195 : lowerHistoryBindingBatch 190 195 := by sorry
