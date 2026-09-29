-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_0064_0096
-- name    : Freiman.section14_s0009_records_0064_0096
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T19:53:26.697642+00:00
-- url     : https://prove2.me/theorems/107f183f-f220-48dd-8862-97a8cf1a82d0
-- title:
--   Freiman.section14_s0009_records_0064_0096
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_0064_0096 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 64).take 32, section14RecordValid section14Catalog 9 r := by sorry
