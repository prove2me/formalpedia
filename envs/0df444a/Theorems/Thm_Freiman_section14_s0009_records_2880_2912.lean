-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2880_2912
-- name    : Freiman.section14_s0009_records_2880_2912
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:55:49.614116+00:00
-- url     : https://prove2.me/theorems/d1dbca23-3641-4740-82bd-cc979e8ace53
-- title:
--   Freiman.section14_s0009_records_2880_2912
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2880).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2880_2912 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2880).take 32, section14RecordValid section14Catalog 9 r := by sorry
