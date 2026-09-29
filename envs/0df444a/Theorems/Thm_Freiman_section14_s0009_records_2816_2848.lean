-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2816_2848
-- name    : Freiman.section14_s0009_records_2816_2848
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:53:33.036871+00:00
-- url     : https://prove2.me/theorems/18011b6b-4241-4d27-bb90-fbc796f385b6
-- title:
--   Freiman.section14_s0009_records_2816_2848
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2816_2848 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 9 r := by sorry
