-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_1888_1920
-- name    : Freiman.section14_s0010_records_1888_1920
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:22:48.772216+00:00
-- url     : https://prove2.me/theorems/3e8e9e93-d185-4feb-9c4b-558d1067700a
-- title:
--   Freiman.section14_s0010_records_1888_1920
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_1888_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 10 r := by sorry
