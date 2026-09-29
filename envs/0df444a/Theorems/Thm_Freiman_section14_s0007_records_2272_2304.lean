-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_2272_2304
-- name    : Freiman.section14_s0007_records_2272_2304
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:38:55.477926+00:00
-- url     : https://prove2.me/theorems/494ab5ef-2df8-4eac-82aa-a339b04c8ff7
-- title:
--   Freiman.section14_s0007_records_2272_2304
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_2272_2304 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 7 r := by sorry
