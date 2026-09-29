-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0155_0160
-- name    : Freiman.lowerHistory_bindings_0155_0160
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:26:13.209084+00:00
-- url     : https://prove2.me/theorems/fcca20c3-9546-42cd-a669-cf934c2eb821
-- title:
--   Freiman lower-history bindings, indices 155–159
-- statement:
--   For every original catalogue index $i$ with $$155\le i<160$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0150_0160, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 155 160`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0150_0160, UUID 89d55d60-2d1f-4915-be2e-afa7d4d0bd01. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 155–159.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0155_0160 : lowerHistoryBindingBatch 155 160 := by sorry
