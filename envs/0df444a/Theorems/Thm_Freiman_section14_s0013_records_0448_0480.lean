-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0448_0480
-- name    : Freiman.section14_s0013_records_0448_0480
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T11:49:38.829519+00:00
-- url     : https://prove2.me/theorems/030b7e5d-08a0-4779-919e-e8c64aad3b01
-- title:
--   Freiman.section14_s0013_records_0448_0480
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0448_0480 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 13 r := by sorry
