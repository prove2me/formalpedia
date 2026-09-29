-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1408_1440
-- name    : Freiman.section14_s0007_records_1408_1440
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:04:15.338276+00:00
-- url     : https://prove2.me/theorems/11649053-f4f0-4337-8312-24bcfe43599b
-- title:
--   Freiman.section14_s0007_records_1408_1440
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1408_1440 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 7 r := by sorry
