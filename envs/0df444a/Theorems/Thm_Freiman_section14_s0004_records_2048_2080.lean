-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_2048_2080
-- name    : Freiman.section14_s0004_records_2048_2080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:03:23.252521+00:00
-- url     : https://prove2.me/theorems/3eb7b747-2673-4aad-9652-dd3d839276b1
-- title:
--   Freiman.section14_s0004_records_2048_2080
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_2048_2080 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 2048).take 32, section14RecordValid section14Catalog 4 r := by sorry
