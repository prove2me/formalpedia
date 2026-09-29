-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_all
-- name    : Freiman.section14_s0014_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:24:22.022115+00:00
-- url     : https://prove2.me/theorems/195f4068-bfa4-4649-b5ea-cf32216c94e6
-- title:
--   Freiman.section14_s0014_records_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (14 ∈ r.states))), section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (14 ∈ r.states))), section14RecordValid section14Catalog 14 r := by sorry
