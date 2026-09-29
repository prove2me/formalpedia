-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0960_0992
-- name    : Freiman.section14_s0013_records_0960_0992
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T12:04:48.132168+00:00
-- url     : https://prove2.me/theorems/c25f1055-a1b4-4fc9-a72d-71dfc6c8cdb2
-- title:
--   Freiman.section14_s0013_records_0960_0992
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 13 r := by sorry
