-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0704_0736
-- name    : Freiman.section14_s0003_records_0704_0736
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:33:59.236535+00:00
-- url     : https://prove2.me/theorems/0ed1bf85-f566-4b12-880b-6b39809237c4
-- title:
--   Freiman.section14_s0003_records_0704_0736
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0704_0736 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 3 r := by sorry
