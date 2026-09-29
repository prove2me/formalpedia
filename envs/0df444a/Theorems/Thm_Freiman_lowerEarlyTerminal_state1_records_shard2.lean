-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state1_records_shard2
-- name    : Freiman.lowerEarlyTerminal_state1_records_shard2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T21:18:22.119507+00:00
-- url     : https://prove2.me/theorems/4df050e5-408b-45c5-8562-7e84704edf61
-- title:
--   Freiman H5: State1 record catalogue, part 2
-- statement:
--   Let $C$ be the State1 early-terminal catalogue and let $R$ be its stored record shard 2. Every record in this shard satisfies the catalogue's exact record-validity conditions:
--
--   $$\forall r\in R,\quad \operatorname{Valid}_C(r).$$
--
--   Record validity means that the goal, branch, pair and bound identifiers are in range; the stored premise set equals the independently reconstructed residual premise set for the selected endpoint branch; and both bounds used by the selected pair occur among those premises. These conditions connect the numerical pair certificates to the endpoint cases needed in the H5 exception-anchor argument.
--
--   **Formalization Note.** The shard is the existing `lowerEarlyTerminalRecordsState102` and validity is the unchanged predicate `lowerEarlyTerminalRecordValid`.
-- source:
--   Freiman lower Hall-ray construction, condition (14.5); project verification report Lemma 7.3, report p.42 (original source p.97). Existing catalogue prerequisite: https://prove2.me/theorem/0f5a21d4-dee3-40f9-8369-213053091f71

import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_state1_records_shard2 : ∀ r ∈ lowerEarlyTerminalRecordsState102, lowerEarlyTerminalRecordValid lowerEarlyTerminalState1 r := by sorry
