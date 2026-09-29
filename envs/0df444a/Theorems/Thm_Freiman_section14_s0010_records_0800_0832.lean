-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0800_0832
-- name    : Freiman.section14_s0010_records_0800_0832
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:49:51.420242+00:00
-- url     : https://prove2.me/theorems/9bd4f1d2-dd8b-4f0a-857f-f8c6972ccc1d
-- title:
--   Freiman.section14_s0010_records_0800_0832
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0800_0832 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 10 r := by sorry
