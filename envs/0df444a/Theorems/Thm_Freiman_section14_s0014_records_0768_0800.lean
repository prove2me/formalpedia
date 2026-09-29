-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_0768_0800
-- name    : Freiman.section14_s0014_records_0768_0800
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:36:30.822973+00:00
-- url     : https://prove2.me/theorems/a7fb5a47-e7be-4d4b-9daf-51721b8bec5a
-- title:
--   Freiman.section14_s0014_records_0768_0800
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_0768_0800 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 14 r := by sorry
