-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0180_0185
-- name    : Freiman.lowerHistory_bindings_0180_0185
-- status  : Proved
-- author  : @tp
-- created : 2026-09-17T19:25:57.672037+00:00
-- url     : https://prove2.me/theorems/245038d6-f618-4351-959e-e5adc7aa43bb
-- title:
--   Freiman lower-history bindings, indices 180–184
-- statement:
--   For every original catalogue index $i$ with $$180\le i<185$$ the path at that index satisfies all original binding and record-coverage conditions. The source alternatives, premise finite sets, witness bounds and witness rectangle are unchanged. This is the indicated five-index restriction of Freiman.lowerHistory_bindings_0180_0190, introduced to keep its complete proof within the verification time limit.
--
--   **Formalization Note** The exact predicate is `lowerHistoryBindingBatch 180 185`.
-- source:
--   Exact subinterval of Freiman.lowerHistory_bindings_0180_0190, UUID 22edb1d6-cbe1-4107-8d4f-35e76063ab49. Original Def_Freiman_lowerHistoryVerification predicate and Def_Freiman_lowerHistoryCatalogL, indices 180–184.

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0180_0185 : lowerHistoryBindingBatch 180 185 := by sorry
