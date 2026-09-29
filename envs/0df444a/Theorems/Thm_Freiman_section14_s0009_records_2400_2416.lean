-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2400_2416
-- name    : Freiman.section14_s0009_records_2400_2416
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:33:19.315931+00:00
-- url     : https://prove2.me/theorems/7ca42b8b-1a0a-479e-9c49-da29314e37f8
-- title:
--   Freiman.section14_s0009_records_2400_2416
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2400).take 16, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2400_2416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2400).take 16, section14RecordValid section14Catalog 9 r := by sorry
