-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0320_0352
-- name    : Freiman.section14_s0013_records_0320_0352
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T11:44:46.35491+00:00
-- url     : https://prove2.me/theorems/571ad1c3-3b7d-4f53-b0e6-2209749b0410
-- title:
--   Freiman.section14_s0013_records_0320_0352
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0320_0352 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 320).take 32, section14RecordValid section14Catalog 13 r := by sorry
