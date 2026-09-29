-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1504_1536
-- name    : Freiman.section14_s0016_records_1504_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:34:33.093849+00:00
-- url     : https://prove2.me/theorems/ec168a0b-2342-4eed-ad2f-ba23831ea65d
-- title:
--   Freiman.section14_s0016_records_1504_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1504_1536 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 16 r := by sorry
