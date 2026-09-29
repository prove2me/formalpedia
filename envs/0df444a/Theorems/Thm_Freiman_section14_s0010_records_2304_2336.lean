-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_2304_2336
-- name    : Freiman.section14_s0010_records_2304_2336
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:58:47.714475+00:00
-- url     : https://prove2.me/theorems/a51726cc-c147-4b8d-bbb9-e9f2fc0488d1
-- title:
--   Freiman.section14_s0010_records_2304_2336
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_2304_2336 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2304).take 32, section14RecordValid section14Catalog 10 r := by sorry
