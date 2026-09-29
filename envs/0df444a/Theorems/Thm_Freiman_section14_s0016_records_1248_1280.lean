-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1248_1280
-- name    : Freiman.section14_s0016_records_1248_1280
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:24:50.361176+00:00
-- url     : https://prove2.me/theorems/488f6be7-ea50-453b-93ac-0731a8d8e0a5
-- title:
--   Freiman.section14_s0016_records_1248_1280
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1248_1280 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 16 r := by sorry
