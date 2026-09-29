-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_1568_1600
-- name    : Freiman.section14_s0007_records_1568_1600
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T10:11:00.972302+00:00
-- url     : https://prove2.me/theorems/611e7100-c30e-4b35-93c1-41ba4d144900
-- title:
--   Freiman.section14_s0007_records_1568_1600
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_1568_1600 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 7 r := by sorry
