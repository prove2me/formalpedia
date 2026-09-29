-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0864_0896
-- name    : Freiman.section14_s0010_records_0864_0896
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:51:53.916842+00:00
-- url     : https://prove2.me/theorems/884b6d43-499b-4ef1-a064-8e16ddf401cc
-- title:
--   Freiman.section14_s0010_records_0864_0896
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0864_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 10 r := by sorry
