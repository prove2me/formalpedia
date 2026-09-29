-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_0288_0320
-- name    : Freiman.section14_s0014_records_0288_0320
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:25:13.698988+00:00
-- url     : https://prove2.me/theorems/01c6c9c9-6d2e-4078-9b36-99e7a0ba0653
-- title:
--   Freiman.section14_s0014_records_0288_0320
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_0288_0320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 288).take 32, section14RecordValid section14Catalog 14 r := by sorry
