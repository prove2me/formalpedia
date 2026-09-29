-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2688_2720
-- name    : Freiman.section14_s0009_records_2688_2720
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:44:41.657282+00:00
-- url     : https://prove2.me/theorems/6b2c8412-e45e-4e65-ab99-9bbd4852e897
-- title:
--   Freiman.section14_s0009_records_2688_2720
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2688_2720 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 9 r := by sorry
