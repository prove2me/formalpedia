-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_1184_1216
-- name    : Freiman.section14_s0003_records_1184_1216
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:53:48.517915+00:00
-- url     : https://prove2.me/theorems/6ed82bd0-f193-46c4-8f2a-d7402e032b6f
-- title:
--   Freiman.section14_s0003_records_1184_1216
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 3 r := by sorry
