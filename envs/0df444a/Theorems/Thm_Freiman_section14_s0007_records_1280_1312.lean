-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1280_1312
-- name    : Freiman.section14_s0007_records_1280_1312
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:00:14.265805+00:00
-- url     : https://prove2.me/theorems/fe933895-940d-4cc6-8bb8-0354cde0260f
-- title:
--   Freiman.section14_s0007_records_1280_1312
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1280_1312 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 7 r := by sorry
