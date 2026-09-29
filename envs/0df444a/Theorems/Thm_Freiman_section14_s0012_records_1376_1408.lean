-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_1376_1408
-- name    : Freiman.section14_s0012_records_1376_1408
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:55:37.882107+00:00
-- url     : https://prove2.me/theorems/c588afa4-bae6-40ea-ba0a-2e380d77ee48
-- title:
--   Freiman.section14_s0012_records_1376_1408
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 12 r := by sorry
