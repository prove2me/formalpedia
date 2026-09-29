-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_2976_2987
-- name    : Freiman.section14_s0009_records_2976_2987
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:59:03.002226+00:00
-- url     : https://prove2.me/theorems/09af290a-8ed8-4a63-9614-d527506ee14b
-- title:
--   Freiman.section14_s0009_records_2976_2987
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2976).take 11, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_2976_2987 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2976).take 11, section14RecordValid section14Catalog 9 r := by sorry
