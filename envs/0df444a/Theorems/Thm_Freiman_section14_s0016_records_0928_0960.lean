-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0928_0960
-- name    : Freiman.section14_s0016_records_0928_0960
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:12:20.074249+00:00
-- url     : https://prove2.me/theorems/e82f7a8a-9e69-40f0-aa7f-f76fa80bd972
-- title:
--   Freiman.section14_s0016_records_0928_0960
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0928_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 16 r := by sorry
