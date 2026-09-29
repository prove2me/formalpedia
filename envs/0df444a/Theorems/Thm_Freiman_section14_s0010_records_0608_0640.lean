-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0608_0640
-- name    : Freiman.section14_s0010_records_0608_0640
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:44:29.166394+00:00
-- url     : https://prove2.me/theorems/ce830d64-e3a0-4329-aa89-95b9a3a1967c
-- title:
--   Freiman.section14_s0010_records_0608_0640
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 10 r := by sorry
