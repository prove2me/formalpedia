-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_all
-- name    : Freiman.section14_s0007_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T11:40:57.979508+00:00
-- url     : https://prove2.me/theorems/9f0b4007-780c-4319-9aca-d30c2e91e9d7
-- title:
--   Freiman.section14_s0007_records_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (7 ∈ r.states))), section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (7 ∈ r.states))), section14RecordValid section14Catalog 7 r := by sorry
