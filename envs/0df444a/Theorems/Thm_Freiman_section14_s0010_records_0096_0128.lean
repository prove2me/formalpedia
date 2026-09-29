-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0096_0128
-- name    : Freiman.section14_s0010_records_0096_0128
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:29:45.967231+00:00
-- url     : https://prove2.me/theorems/c1e2b9b0-149f-40f5-b498-8a6f71f3071f
-- title:
--   Freiman.section14_s0010_records_0096_0128
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0096_0128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 10 r := by sorry
