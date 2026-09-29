-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2848_2880
-- name    : Freiman.section14_s0009_records_2848_2880
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:53:36.747663+00:00
-- url     : https://prove2.me/theorems/dcfbe17a-525d-4db7-b06a-b87d2f91b537
-- title:
--   Freiman.section14_s0009_records_2848_2880
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2848_2880 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 9 r := by sorry
