-- Prove2me | Theorems.Thm_Freiman_section14_s0011_records_0160_0224
-- name    : Freiman.section14_s0011_records_0160_0224
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T12:19:30.090446+00:00
-- url     : https://prove2.me/theorems/8e7ebd38-5ac6-4f56-a118-f14ff5a24b59
-- title:
--   Freiman.section14_s0011_records_0160_0224
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 160).take 64, section14RecordValid section14Catalog 11 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_records_0160_0224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 160).take 64, section14RecordValid section14Catalog 11 r := by sorry
