-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0576_0608
-- name    : Freiman.section14_s0007_records_0576_0608
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:30:25.345637+00:00
-- url     : https://prove2.me/theorems/81ca0e2c-4e0f-45ae-b157-f64884182ef7
-- title:
--   Freiman.section14_s0007_records_0576_0608
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 7 r := by sorry
