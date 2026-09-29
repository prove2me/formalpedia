-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_2240_2272
-- name    : Freiman.section14_s0012_records_2240_2272
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:26:51.871752+00:00
-- url     : https://prove2.me/theorems/faec936d-891a-4d38-ae69-f5811faffa9c
-- title:
--   Freiman.section14_s0012_records_2240_2272
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_2240_2272 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 12 r := by sorry
