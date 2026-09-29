-- Prove2me | Theorems.Thm_Freiman_section14_s0011_records_0352_0416
-- name    : Freiman.section14_s0011_records_0352_0416
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T12:31:21.074268+00:00
-- url     : https://prove2.me/theorems/235997c7-a63a-46a0-bfa5-57039b8ac5e4
-- title:
--   Freiman.section14_s0011_records_0352_0416
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 352).take 64, section14RecordValid section14Catalog 11 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_records_0352_0416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 352).take 64, section14RecordValid section14Catalog 11 r := by sorry
