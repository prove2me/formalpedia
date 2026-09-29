-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1792_1824
-- name    : Freiman.section14_s0016_records_1792_1824
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:46:57.917499+00:00
-- url     : https://prove2.me/theorems/23bb5fc6-d9ae-4c9b-8a9f-434384994ca0
-- title:
--   Freiman.section14_s0016_records_1792_1824
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1792_1824 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 16 r := by sorry
