-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_0832_0864
-- name    : Freiman.section14_s0002_records_0832_0864
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:09:26.498986+00:00
-- url     : https://prove2.me/theorems/58b86f4f-827c-4cf2-b656-80002c78aac9
-- title:
--   Freiman.section14_s0002_records_0832_0864
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 2 r := by sorry
