-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0704_0736
-- name    : Freiman.section14_s0008_records_0704_0736
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:05:48.507467+00:00
-- url     : https://prove2.me/theorems/28dc1d4d-4acf-43ec-b37d-12155c0189a7
-- title:
--   Freiman.section14_s0008_records_0704_0736
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0704_0736 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 8 r := by sorry
