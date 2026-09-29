-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_1696_1728
-- name    : Freiman.section14_s0008_records_1696_1728
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:37:28.89192+00:00
-- url     : https://prove2.me/theorems/eef3eb84-5046-45e3-8a0a-4ba3f3383edd
-- title:
--   Freiman.section14_s0008_records_1696_1728
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_1696_1728 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 8 r := by sorry
