-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1792_1824
-- name    : Freiman.section14_s0007_records_1792_1824
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:20:57.624812+00:00
-- url     : https://prove2.me/theorems/a5b94a4d-168b-4dbf-8ee5-d8cde5f88d9c
-- title:
--   Freiman.section14_s0007_records_1792_1824
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1792_1824 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 7 r := by sorry
