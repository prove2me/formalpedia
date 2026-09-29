-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_0096_0128
-- name    : Freiman.section14_s0015_records_0096_0128
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:39:50.903129+00:00
-- url     : https://prove2.me/theorems/b737f0d5-f907-4f91-96e1-4c01e3212844
-- title:
--   Freiman.section14_s0015_records_0096_0128
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_0096_0128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 15 r := by sorry
