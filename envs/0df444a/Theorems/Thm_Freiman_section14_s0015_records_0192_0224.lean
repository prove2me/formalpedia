-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_0192_0224
-- name    : Freiman.section14_s0015_records_0192_0224
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:45:13.948019+00:00
-- url     : https://prove2.me/theorems/a35f75b4-7420-41aa-a3f2-ffb9f36bc6cc
-- title:
--   Freiman.section14_s0015_records_0192_0224
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_0192_0224 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 15 r := by sorry
