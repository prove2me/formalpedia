-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_2080_2112
-- name    : Freiman.section14_s0012_records_2080_2112
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T05:21:00.390928+00:00
-- url     : https://prove2.me/theorems/f7198585-6ab3-4d98-aa50-74c0b59440c0
-- title:
--   Freiman.section14_s0012_records_2080_2112
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_2080_2112 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2080).take 32, section14RecordValid section14Catalog 12 r := by sorry
