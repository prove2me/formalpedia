-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0320_0352
-- name    : Freiman.section14_s0010_records_0320_0352
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:36:38.823807+00:00
-- url     : https://prove2.me/theorems/6fec2d1f-517b-4a6d-8e28-7a027f3a43a3
-- title:
--   Freiman.section14_s0010_records_0320_0352
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0320_0352 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 10 r := by sorry
