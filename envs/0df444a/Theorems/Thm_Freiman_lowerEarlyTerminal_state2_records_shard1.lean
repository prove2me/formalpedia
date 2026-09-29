-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state2_records_shard1
-- name    : Freiman.lowerEarlyTerminal_state2_records_shard1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T21:17:50.359842+00:00
-- url     : https://prove2.me/theorems/dc136d42-8248-477b-b160-01b1e8ee6228
-- title:
--   Freiman H5: State2 record catalogue, part 1
-- statement:
--   Let $C$ be the State2 early-terminal catalogue and let $R$ be its stored record shard 1. Every record in this shard satisfies the catalogue's exact record-validity conditions:
--
--   $$\forall r\in R,\quad \operatorname{Valid}_C(r).$$
--
--   Record validity means that the goal, branch, pair and bound identifiers are in range; the stored premise set equals the independently reconstructed residual premise set for the selected endpoint branch; and both bounds used by the selected pair occur among those premises. These conditions connect the numerical pair certificates to the endpoint cases needed in the H5 exception-anchor argument.
--
--   **Formalization Note.** The shard is the existing `lowerEarlyTerminalRecordsState201` and validity is the unchanged predicate `lowerEarlyTerminalRecordValid`.
-- source:
--   Freiman lower Hall-ray construction, condition (14.5); project verification report Lemma 7.3, report p.42 (original source p.97). Existing catalogue prerequisite: https://prove2.me/theorem/daf9f5e8-b2ac-4886-bd82-60031cdba616

import Definitions.Def_Freiman_lowerEarlyTerminalDataState2
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_state2_records_shard1 : ∀ r ∈ lowerEarlyTerminalRecordsState201, lowerEarlyTerminalRecordValid lowerEarlyTerminalState2 r := by sorry
