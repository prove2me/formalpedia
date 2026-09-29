-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0416_0448
-- name    : Freiman.section14_s0003_records_0416_0448
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:27:03.265439+00:00
-- url     : https://prove2.me/theorems/7b6565b6-f562-4e08-bf41-03465b18c90b
-- title:
--   Freiman.section14_s0003_records_0416_0448
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0416_0448 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 3 r := by sorry
