-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_2624_2641
-- name    : Freiman.section14_s0003_records_2624_2641
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:53:02.068864+00:00
-- url     : https://prove2.me/theorems/b0b5d537-f2c9-4e5c-acf2-a66c4661fef1
-- title:
--   Freiman.section14_s0003_records_2624_2641
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2624).take 17, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_2624_2641 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2624).take 17, section14RecordValid section14Catalog 3 r := by sorry
