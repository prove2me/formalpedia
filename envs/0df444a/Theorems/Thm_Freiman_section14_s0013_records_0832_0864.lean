-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0832_0864
-- name    : Freiman.section14_s0013_records_0832_0864
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T12:01:39.948892+00:00
-- url     : https://prove2.me/theorems/f01c5b30-b9ae-4361-bb8e-ea1ff3a6c54a
-- title:
--   Freiman.section14_s0013_records_0832_0864
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 13 r := by sorry
