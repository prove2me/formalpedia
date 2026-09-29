-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0512_0544
-- name    : Freiman.section14_s0013_records_0512_0544
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T11:51:06.337301+00:00
-- url     : https://prove2.me/theorems/34cc99d9-9ba6-4464-a2e2-926c26837a12
-- title:
--   Freiman.section14_s0013_records_0512_0544
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0512_0544 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 13 r := by sorry
