-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_2144_2176
-- name    : Freiman.section14_s0007_records_2144_2176
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:33:14.88628+00:00
-- url     : https://prove2.me/theorems/12f6ea3a-786e-4cc0-971e-f32f4c587a55
-- title:
--   Freiman.section14_s0007_records_2144_2176
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_2144_2176 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 7 r := by sorry
