-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1088_1120
-- name    : Freiman.section14_s0002_records_1088_1120
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:16:28.037723+00:00
-- url     : https://prove2.me/theorems/829bceb8-bb87-4e11-9c91-37c89c503609
-- title:
--   Freiman.section14_s0002_records_1088_1120
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 2 r := by sorry
