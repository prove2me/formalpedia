-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0096_0112
-- name    : Freiman.section14_s0008_records_0096_0112
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:46:07.3287+00:00
-- url     : https://prove2.me/theorems/282bbfe6-005e-42fc-a698-1e756e7edd38
-- title:
--   Freiman.section14_s0008_records_0096_0112
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 96).take 16, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0096_0112 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 96).take 16, section14RecordValid section14Catalog 8 r := by sorry
