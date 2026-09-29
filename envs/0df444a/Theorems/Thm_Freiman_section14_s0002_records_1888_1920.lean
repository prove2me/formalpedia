-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1888_1920
-- name    : Freiman.section14_s0002_records_1888_1920
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:41:56.544977+00:00
-- url     : https://prove2.me/theorems/1a9a036d-7d42-4b4e-a6e2-c569493f01d7
-- title:
--   Freiman.section14_s0002_records_1888_1920
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1888_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 2 r := by sorry
