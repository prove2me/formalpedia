-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_1408_1440
-- name    : Freiman.section14_s0009_records_1408_1440
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:44:13.037308+00:00
-- url     : https://prove2.me/theorems/a537bcff-7099-4c46-a8d8-fc9c9502150b
-- title:
--   Freiman.section14_s0009_records_1408_1440
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_1408_1440 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 9 r := by sorry
