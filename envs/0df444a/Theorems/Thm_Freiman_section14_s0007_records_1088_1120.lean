-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1088_1120
-- name    : Freiman.section14_s0007_records_1088_1120
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:51:49.197384+00:00
-- url     : https://prove2.me/theorems/917da8d2-e0be-44b4-8ce3-da6dbe2ac7b8
-- title:
--   Freiman.section14_s0007_records_1088_1120
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 7 r := by sorry
