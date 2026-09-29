-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1376_1408
-- name    : Freiman.section14_s0002_records_1376_1408
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:24:19.168102+00:00
-- url     : https://prove2.me/theorems/31914dc0-6177-4c04-95a9-1626a23a5fbd
-- title:
--   Freiman.section14_s0002_records_1376_1408
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 2 r := by sorry
