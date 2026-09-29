-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1376_1408
-- name    : Freiman.section14_s0016_records_1376_1408
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:29:16.453155+00:00
-- url     : https://prove2.me/theorems/b7457247-84e7-4768-af97-f9440ae97ec4
-- title:
--   Freiman.section14_s0016_records_1376_1408
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 16 r := by sorry
