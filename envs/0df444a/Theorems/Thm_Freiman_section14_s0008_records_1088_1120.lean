-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_1088_1120
-- name    : Freiman.section14_s0008_records_1088_1120
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:16:08.878774+00:00
-- url     : https://prove2.me/theorems/89786aa7-0441-48d4-96b5-d9210c2e3ea1
-- title:
--   Freiman.section14_s0008_records_1088_1120
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 8 r := by sorry
