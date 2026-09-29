-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0416_0448
-- name    : Freiman.section14_s0008_records_0416_0448
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:56:25.787668+00:00
-- url     : https://prove2.me/theorems/71f24bb7-fe8e-4ea6-b145-025a71f68d6a
-- title:
--   Freiman.section14_s0008_records_0416_0448
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0416_0448 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 8 r := by sorry
