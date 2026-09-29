-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_2560_2580
-- name    : Freiman.section14_s0008_records_2560_2580
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:07:45.415989+00:00
-- url     : https://prove2.me/theorems/56cc8b9b-a73d-40a7-9789-4b1365803ad3
-- title:
--   Freiman.section14_s0008_records_2560_2580
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2560).take 20, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_2560_2580 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2560).take 20, section14RecordValid section14Catalog 8 r := by sorry
