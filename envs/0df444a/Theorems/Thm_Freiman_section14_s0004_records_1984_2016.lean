-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_1984_2016
-- name    : Freiman.section14_s0004_records_1984_2016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:01:15.890008+00:00
-- url     : https://prove2.me/theorems/7bc1e73b-aa73-4764-b627-c9f2aa3c36e1
-- title:
--   Freiman.section14_s0004_records_1984_2016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_1984_2016 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1984).take 32, section14RecordValid section14Catalog 4 r := by sorry
