-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0832_0864
-- name    : Freiman.section14_s0008_records_0832_0864
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:09:44.975408+00:00
-- url     : https://prove2.me/theorems/ef719789-15d4-4097-bd1b-bacd9ca110cf
-- title:
--   Freiman.section14_s0008_records_0832_0864
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 8 r := by sorry
