-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0960_0992
-- name    : Freiman.section14_s0003_records_0960_0992
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:44:43.305484+00:00
-- url     : https://prove2.me/theorems/73547a50-4c10-40cd-ba23-ca085027a85c
-- title:
--   Freiman.section14_s0003_records_0960_0992
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0960_0992 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 960).take 32, section14RecordValid section14Catalog 3 r := by sorry
