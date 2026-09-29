-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1184_1216
-- name    : Freiman.section14_s0002_records_1184_1216
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:18:59.487985+00:00
-- url     : https://prove2.me/theorems/6bf5419f-4ae4-46c5-aed7-e4e5b04ba36e
-- title:
--   Freiman.section14_s0002_records_1184_1216
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 2 r := by sorry
