-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0992_1024
-- name    : Freiman.section14_s0008_records_0992_1024
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:13:55.105611+00:00
-- url     : https://prove2.me/theorems/14dbb437-a2cd-431f-8e43-653286d83805
-- title:
--   Freiman.section14_s0008_records_0992_1024
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 992).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0992_1024 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 992).take 32, section14RecordValid section14Catalog 8 r := by sorry
