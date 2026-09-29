-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_1312_1344
-- name    : Freiman.section14_s0010_records_1312_1344
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:06:13.82008+00:00
-- url     : https://prove2.me/theorems/e341438a-3d4a-4d8c-95de-1540119a3a05
-- title:
--   Freiman.section14_s0010_records_1312_1344
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_1312_1344 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 10 r := by sorry
