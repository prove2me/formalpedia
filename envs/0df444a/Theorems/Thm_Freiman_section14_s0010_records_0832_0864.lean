-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0832_0864
-- name    : Freiman.section14_s0010_records_0832_0864
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:50:41.918221+00:00
-- url     : https://prove2.me/theorems/102d8ccc-0973-4ce7-8d30-89110edd305d
-- title:
--   Freiman.section14_s0010_records_0832_0864
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 10 r := by sorry
