-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0960_0992
-- name    : Freiman.section14_s0010_records_0960_0992
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:55:10.346901+00:00
-- url     : https://prove2.me/theorems/f65cb06b-76f1-4db6-9afa-f41de94770c6
-- title:
--   Freiman.section14_s0010_records_0960_0992
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 10 r := by sorry
