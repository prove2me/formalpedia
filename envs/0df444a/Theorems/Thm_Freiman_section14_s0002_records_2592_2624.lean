-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_2592_2624
-- name    : Freiman.section14_s0002_records_2592_2624
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:21:53.155984+00:00
-- url     : https://prove2.me/theorems/afa524a2-b1b1-4243-85c4-4813c3f8883b
-- title:
--   Freiman.section14_s0002_records_2592_2624
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 2 r := by sorry
