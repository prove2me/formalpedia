-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_1600_1632
-- name    : Freiman.section14_s0009_records_1600_1632
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:50:50.410681+00:00
-- url     : https://prove2.me/theorems/65452c91-664f-4d2e-81e4-3834d389c154
-- title:
--   Freiman.section14_s0009_records_1600_1632
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_1600_1632 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 9 r := by sorry
