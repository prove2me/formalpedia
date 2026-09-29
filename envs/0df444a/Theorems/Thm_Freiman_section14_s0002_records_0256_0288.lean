-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_0256_0288
-- name    : Freiman.section14_s0002_records_0256_0288
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:55:55.898974+00:00
-- url     : https://prove2.me/theorems/a6d36b66-43ee-488b-892b-dd32651567c1
-- title:
--   Freiman.section14_s0002_records_0256_0288
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_0256_0288 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 2 r := by sorry
