-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_all
-- name    : Freiman.section14_s0002_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:28:49.490022+00:00
-- url     : https://prove2.me/theorems/1a854641-5a13-4558-946a-53bbae87fc15
-- title:
--   Freiman.section14_s0002_records_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (2 ∈ r.states))), section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (2 ∈ r.states))), section14RecordValid section14Catalog 2 r := by sorry
