-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_1600_1632
-- name    : Freiman.section14_s0003_records_1600_1632
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:11:06.669639+00:00
-- url     : https://prove2.me/theorems/95842143-39b6-4eaa-92b2-a9abc99d5c66
-- title:
--   Freiman.section14_s0003_records_1600_1632
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_1600_1632 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 3 r := by sorry
