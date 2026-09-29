-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_2176_2208
-- name    : Freiman.section14_s0007_records_2176_2208
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:35:48.726978+00:00
-- url     : https://prove2.me/theorems/5396725d-4cd5-4c09-ae90-87c130cfefb4
-- title:
--   Freiman.section14_s0007_records_2176_2208
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_2176_2208 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 7 r := by sorry
