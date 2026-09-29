-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_0000_0032
-- name    : Freiman.section14_s0014_records_0000_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:18:09.65653+00:00
-- url     : https://prove2.me/theorems/3b54fdef-7fb1-44c2-8f17-055e4f957c81
-- title:
--   Freiman.section14_s0014_records_0000_0032
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_0000_0032 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 14 r := by sorry
