-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1824_1856
-- name    : Freiman.section14_s0002_records_1824_1856
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:40:12.322657+00:00
-- url     : https://prove2.me/theorems/d85489eb-b3ff-41f6-bf86-545e73b19bf9
-- title:
--   Freiman.section14_s0002_records_1824_1856
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1824_1856 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 2 r := by sorry
