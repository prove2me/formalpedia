-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_1824_1856
-- name    : Freiman.section14_s0009_records_1824_1856
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T21:03:16.183082+00:00
-- url     : https://prove2.me/theorems/c5135bad-56bc-4a96-80c5-fdb9197f8790
-- title:
--   Freiman.section14_s0009_records_1824_1856
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_1824_1856 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 9 r := by sorry
