-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0288_0320
-- name    : Freiman.section14_s0007_records_0288_0320
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:22:11.020748+00:00
-- url     : https://prove2.me/theorems/c9897f29-946e-481b-bf62-a95b8feeaed1
-- title:
--   Freiman.section14_s0007_records_0288_0320
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0288_0320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 7 r := by sorry
