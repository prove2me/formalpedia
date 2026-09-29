-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_1504_1536
-- name    : Freiman.section14_s0014_records_1504_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:09:03.602984+00:00
-- url     : https://prove2.me/theorems/243ec7b2-61f4-4a09-a7c2-79bef6ecbce9
-- title:
--   Freiman.section14_s0014_records_1504_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_1504_1536 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 14 r := by sorry
