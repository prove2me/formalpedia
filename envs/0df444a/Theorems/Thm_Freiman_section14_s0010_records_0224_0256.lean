-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0224_0256
-- name    : Freiman.section14_s0010_records_0224_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:33:42.914953+00:00
-- url     : https://prove2.me/theorems/163402dd-30f2-4d9a-bd92-709ab09c62d3
-- title:
--   Freiman.section14_s0010_records_0224_0256
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0224_0256 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 10 r := by sorry
