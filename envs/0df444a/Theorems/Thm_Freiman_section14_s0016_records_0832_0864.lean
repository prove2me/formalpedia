-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0832_0864
-- name    : Freiman.section14_s0016_records_0832_0864
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:07:30.762527+00:00
-- url     : https://prove2.me/theorems/0eb7ae27-89bd-4ae9-8374-a2e77eb5e1f8
-- title:
--   Freiman.section14_s0016_records_0832_0864
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 16 r := by sorry
