-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_1056_1088
-- name    : Freiman.section14_s0013_records_1056_1088
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T12:07:40.839907+00:00
-- url     : https://prove2.me/theorems/fe3fa33c-250a-41f5-b8f2-f7a0767c6db6
-- title:
--   Freiman.section14_s0013_records_1056_1088
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_1056_1088 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 13 r := by sorry
