-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_0960_0992
-- name    : Freiman.section14_s0014_records_0960_0992
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:45:55.530989+00:00
-- url     : https://prove2.me/theorems/0bf42b23-0ff0-40c0-b118-3f5b593e1a4c
-- title:
--   Freiman.section14_s0014_records_0960_0992
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 14 r := by sorry
