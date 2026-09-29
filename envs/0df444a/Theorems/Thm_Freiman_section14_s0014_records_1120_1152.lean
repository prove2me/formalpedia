-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_1120_1152
-- name    : Freiman.section14_s0014_records_1120_1152
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:53:47.390629+00:00
-- url     : https://prove2.me/theorems/fd8b498f-52b6-4546-8e7a-2a3c8d1d3dbf
-- title:
--   Freiman.section14_s0014_records_1120_1152
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_1120_1152 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 14 r := by sorry
