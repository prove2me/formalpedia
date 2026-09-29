-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0384_0416
-- name    : Freiman.section14_s0007_records_0384_0416
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:24:47.524585+00:00
-- url     : https://prove2.me/theorems/b4e57fc0-466b-407d-93fc-7ad52da5f954
-- title:
--   Freiman.section14_s0007_records_0384_0416
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0384_0416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 7 r := by sorry
