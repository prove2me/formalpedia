-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_1376_1408
-- name    : Freiman.section14_s0003_records_1376_1408
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:01:38.808498+00:00
-- url     : https://prove2.me/theorems/ea1001dc-4a8c-472f-a33a-0c0f37d968a1
-- title:
--   Freiman.section14_s0003_records_1376_1408
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 3 r := by sorry
