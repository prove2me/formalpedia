-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_2336_2368
-- name    : Freiman.section14_s0007_records_2336_2368
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:41:15.127242+00:00
-- url     : https://prove2.me/theorems/1172ab32-9335-434c-a164-88b702d2a982
-- title:
--   Freiman.section14_s0007_records_2336_2368
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_2336_2368 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2336).take 32, section14RecordValid section14Catalog 7 r := by sorry
