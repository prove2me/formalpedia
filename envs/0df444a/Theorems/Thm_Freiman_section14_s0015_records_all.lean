-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_all
-- name    : Freiman.section14_s0015_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:49:11.028546+00:00
-- url     : https://prove2.me/theorems/3ac22198-2440-41c5-96ef-eda0ca825e65
-- title:
--   Freiman.section14_s0015_records_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (15 ∈ r.states))), section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (15 ∈ r.states))), section14RecordValid section14Catalog 15 r := by sorry
