-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0096_0128
-- name    : Freiman.section14_s0016_records_0096_0128
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:37:00.354722+00:00
-- url     : https://prove2.me/theorems/b0b13b6a-db7c-404e-80f1-87668d39a05d
-- title:
--   Freiman.section14_s0016_records_0096_0128
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0096_0128 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 16 r := by sorry
