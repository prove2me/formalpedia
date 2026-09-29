-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_2496_2528
-- name    : Freiman.section14_s0008_records_2496_2528
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:05:43.604982+00:00
-- url     : https://prove2.me/theorems/b46807ce-0b1a-403d-a8c9-a15d2d589bdb
-- title:
--   Freiman.section14_s0008_records_2496_2528
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_2496_2528 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 8 r := by sorry
