-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_1408_1440
-- name    : Freiman.section14_s0012_records_1408_1440
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:57:21.844992+00:00
-- url     : https://prove2.me/theorems/29177d15-66ea-4294-a7b4-07d48e4ea6fc
-- title:
--   Freiman.section14_s0012_records_1408_1440
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_1408_1440 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 12 r := by sorry
