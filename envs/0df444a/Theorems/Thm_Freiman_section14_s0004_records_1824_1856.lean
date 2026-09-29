-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_1824_1856
-- name    : Freiman.section14_s0004_records_1824_1856
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T02:54:47.709129+00:00
-- url     : https://prove2.me/theorems/cb60629c-de79-4fa0-9229-02061bc9ff4f
-- title:
--   Freiman.section14_s0004_records_1824_1856
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_1824_1856 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 4 r := by sorry
