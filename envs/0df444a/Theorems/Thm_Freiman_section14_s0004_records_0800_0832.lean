-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_0800_0832
-- name    : Freiman.section14_s0004_records_0800_0832
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T02:19:30.805919+00:00
-- url     : https://prove2.me/theorems/a1da84b3-60e6-4ce5-86ac-6d7a2bed8208
-- title:
--   Freiman.section14_s0004_records_0800_0832
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_0800_0832 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 4 r := by sorry
