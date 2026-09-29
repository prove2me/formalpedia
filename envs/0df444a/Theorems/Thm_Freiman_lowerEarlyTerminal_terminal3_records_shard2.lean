-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_records_shard2
-- name    : Freiman.lowerEarlyTerminal_terminal3_records_shard2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-13T21:18:02.063289+00:00
-- url     : https://prove2.me/theorems/740f119f-82b2-4456-8a40-963a95ff05f4
-- title:
--   Freiman H5: Terminal3 record catalogue, part 2
-- statement:
--   Let $C$ be the Terminal3 early-terminal catalogue and let $R$ be its stored record shard 2. Every record in this shard satisfies the catalogue's exact record-validity conditions:
--
--   $$\forall r\in R,\quad \operatorname{Valid}_C(r).$$
--
--   Record validity means that the goal, branch, pair and bound identifiers are in range; the stored premise set equals the independently reconstructed residual premise set for the selected endpoint branch; and both bounds used by the selected pair occur among those premises. These conditions connect the numerical pair certificates to the endpoint cases needed in the H5 exception-anchor argument.
--
--   **Formalization Note.** The shard is the existing `lowerEarlyTerminalRecordsTerminal302` and validity is the unchanged predicate `lowerEarlyTerminalRecordValid`.
-- source:
--   Freiman lower Hall-ray construction, condition (14.5); project verification report Lemma 7.3, report p.42 (original source p.97). Existing catalogue prerequisite: https://prove2.me/theorem/4cfde0d3-870e-41d2-a611-728588c4d3ac

import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman

theorem Freiman.lowerEarlyTerminal_terminal3_records_shard2 : ∀ r ∈ lowerEarlyTerminalRecordsTerminal302, lowerEarlyTerminalRecordValid lowerEarlyTerminalTerminal3 r := by sorry
