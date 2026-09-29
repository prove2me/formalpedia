-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_1504_1536
-- name    : Freiman.section14_s0009_records_1504_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:47:08.519851+00:00
-- url     : https://prove2.me/theorems/1745c6db-bd56-4335-87bd-2218b9c1d4fd
-- title:
--   Freiman.section14_s0009_records_1504_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_1504_1536 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 9 r := by sorry
