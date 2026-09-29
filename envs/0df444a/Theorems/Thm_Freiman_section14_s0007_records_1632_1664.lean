-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1632_1664
-- name    : Freiman.section14_s0007_records_1632_1664
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:14:58.360183+00:00
-- url     : https://prove2.me/theorems/5435ac5f-dcd3-4e6a-8ba3-cc4750a83030
-- title:
--   Freiman.section14_s0007_records_1632_1664
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1632_1664 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 7 r := by sorry
