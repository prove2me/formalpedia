-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_1312_1344
-- name    : Freiman.section14_s0014_records_1312_1344
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:02:11.389003+00:00
-- url     : https://prove2.me/theorems/73e7681e-82c3-43b8-ad40-73d09f0529d3
-- title:
--   Freiman.section14_s0014_records_1312_1344
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_1312_1344 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 14 r := by sorry
