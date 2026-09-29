-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0928_0960
-- name    : Freiman.section14_s0008_records_0928_0960
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:11:37.218817+00:00
-- url     : https://prove2.me/theorems/59e4e91a-7445-4712-bbd6-a36b3f20920a
-- title:
--   Freiman.section14_s0008_records_0928_0960
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0928_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 8 r := by sorry
