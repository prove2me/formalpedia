-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0320_0352
-- name    : Freiman.section14_s0007_records_0320_0352
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:22:51.55188+00:00
-- url     : https://prove2.me/theorems/4d7b02b0-9399-4f12-9ea1-859206f7e45a
-- title:
--   Freiman.section14_s0007_records_0320_0352
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0320_0352 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 7 r := by sorry
