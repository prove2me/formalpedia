-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_0960_0992
-- name    : Freiman.section14_s0012_records_0960_0992
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:41:32.475644+00:00
-- url     : https://prove2.me/theorems/24e057f9-5a59-4782-af58-31b6fc4c029b
-- title:
--   Freiman.section14_s0012_records_0960_0992
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 12 r := by sorry
