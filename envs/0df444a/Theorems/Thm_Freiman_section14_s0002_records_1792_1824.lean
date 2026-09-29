-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_1792_1824
-- name    : Freiman.section14_s0002_records_1792_1824
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:38:52.645862+00:00
-- url     : https://prove2.me/theorems/0f52fa29-2df8-4d2d-a6a7-205e84229db8
-- title:
--   Freiman.section14_s0002_records_1792_1824
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_1792_1824 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 2 r := by sorry
