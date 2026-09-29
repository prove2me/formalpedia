-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_1120_1152
-- name    : Freiman.section14_s0012_records_1120_1152
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:47:17.480602+00:00
-- url     : https://prove2.me/theorems/f9d209e8-5652-489f-9a29-c5eb0de02c89
-- title:
--   Freiman.section14_s0012_records_1120_1152
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_1120_1152 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 12 r := by sorry
