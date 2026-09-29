-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2464_2496
-- name    : Freiman.section14_s0009_records_2464_2496
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:32:38.342564+00:00
-- url     : https://prove2.me/theorems/17917678-2b8c-43ac-8892-c1fec7c3354a
-- title:
--   Freiman.section14_s0009_records_2464_2496
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2464_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 9 r := by sorry
