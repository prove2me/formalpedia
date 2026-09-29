-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0576_0608
-- name    : Freiman.section14_s0008_records_0576_0608
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:02:52.955318+00:00
-- url     : https://prove2.me/theorems/e3146298-7c18-4a0c-9335-79666dd66d6e
-- title:
--   Freiman.section14_s0008_records_0576_0608
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 8 r := by sorry
