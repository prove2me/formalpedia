-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_2400_2432
-- name    : Freiman.section14_s0008_records_2400_2432
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:02:30.514984+00:00
-- url     : https://prove2.me/theorems/4b2f79aa-306f-4250-81d6-c12fb860757f
-- title:
--   Freiman.section14_s0008_records_2400_2432
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_2400_2432 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 8 r := by sorry
