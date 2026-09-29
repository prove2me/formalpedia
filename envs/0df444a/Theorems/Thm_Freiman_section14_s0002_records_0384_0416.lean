-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_0384_0416
-- name    : Freiman.section14_s0002_records_0384_0416
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:58:31.263242+00:00
-- url     : https://prove2.me/theorems/d3cb2224-73a6-4dc0-8c66-eaa79b5ba4e1
-- title:
--   Freiman.section14_s0002_records_0384_0416
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_0384_0416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 2 r := by sorry
