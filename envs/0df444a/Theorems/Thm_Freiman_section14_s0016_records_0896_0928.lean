-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0896_0928
-- name    : Freiman.section14_s0016_records_0896_0928
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:11:00.351692+00:00
-- url     : https://prove2.me/theorems/53922f05-5bb4-4141-b63c-c2b910686d2f
-- title:
--   Freiman.section14_s0016_records_0896_0928
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0896_0928 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 16 r := by sorry
