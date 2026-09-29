-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0288_0320
-- name    : Freiman.section14_s0003_records_0288_0320
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:22:11.875174+00:00
-- url     : https://prove2.me/theorems/c793a5e5-eec6-4fcf-bf31-4d0a439d82c4
-- title:
--   Freiman.section14_s0003_records_0288_0320
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0288_0320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 3 r := by sorry
