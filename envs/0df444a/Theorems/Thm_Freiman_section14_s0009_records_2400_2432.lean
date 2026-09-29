-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2400_2432
-- name    : Freiman.section14_s0009_records_2400_2432
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:29:30.60085+00:00
-- url     : https://prove2.me/theorems/432ac502-b9ee-4bcb-9ad7-1649b1e687ed
-- title:
--   Freiman.section14_s0009_records_2400_2432
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2400_2432 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 9 r := by sorry
