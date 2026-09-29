-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_1760_1792
-- name    : Freiman.section14_s0008_records_1760_1792
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:38:54.26482+00:00
-- url     : https://prove2.me/theorems/876d5420-fd38-4e85-82d0-70c43b8cc953
-- title:
--   Freiman.section14_s0008_records_1760_1792
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_1760_1792 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 8 r := by sorry
