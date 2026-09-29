-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_0192_0224
-- name    : Freiman.section14_s0004_records_0192_0224
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T02:04:28.656984+00:00
-- url     : https://prove2.me/theorems/a2539dcd-b010-4d56-a2b1-2e7cdd02b50c
-- title:
--   Freiman.section14_s0004_records_0192_0224
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_0192_0224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 4 r := by sorry
