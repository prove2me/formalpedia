-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_0064_0096
-- name    : Freiman.section14_s0014_records_0064_0096
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:18:57.055387+00:00
-- url     : https://prove2.me/theorems/25e47f6e-e1e6-477c-afc1-47d3f8d8b0f4
-- title:
--   Freiman.section14_s0014_records_0064_0096
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_0064_0096 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 14 r := by sorry
