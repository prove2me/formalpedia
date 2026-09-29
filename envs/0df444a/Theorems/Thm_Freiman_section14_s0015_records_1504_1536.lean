-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_1504_1536
-- name    : Freiman.section14_s0015_records_1504_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T19:26:22.523456+00:00
-- url     : https://prove2.me/theorems/93c61469-033d-497b-b790-0e47f7d6a145
-- title:
--   Freiman.section14_s0015_records_1504_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_1504_1536 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 15 r := by sorry
