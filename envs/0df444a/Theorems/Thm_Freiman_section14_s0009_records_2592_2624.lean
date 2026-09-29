-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2592_2624
-- name    : Freiman.section14_s0009_records_2592_2624
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:37:04.031609+00:00
-- url     : https://prove2.me/theorems/1b4e8814-4347-4ecd-8732-c5d42dd7f902
-- title:
--   Freiman.section14_s0009_records_2592_2624
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 9 r := by sorry
