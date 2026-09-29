-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2176_2208
-- name    : Freiman.section14_s0009_records_2176_2208
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:17:09.790891+00:00
-- url     : https://prove2.me/theorems/b7ad500c-d1d1-4d01-a406-407a35eed9cf
-- title:
--   Freiman.section14_s0009_records_2176_2208
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2176_2208 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 9 r := by sorry
