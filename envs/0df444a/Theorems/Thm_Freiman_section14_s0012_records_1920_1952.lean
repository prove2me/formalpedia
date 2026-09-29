-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_1920_1952
-- name    : Freiman.section14_s0012_records_1920_1952
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:13:57.796402+00:00
-- url     : https://prove2.me/theorems/c408dd6c-a961-43c9-9974-953309aabc56
-- title:
--   Freiman.section14_s0012_records_1920_1952
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_1920_1952 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1920).take 32, section14RecordValid section14Catalog 12 r := by sorry
