-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1728_1760
-- name    : Freiman.section14_s0016_records_1728_1760
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:44:33.075802+00:00
-- url     : https://prove2.me/theorems/0d0d1944-1213-4684-b941-d20b1be9196a
-- title:
--   Freiman.section14_s0016_records_1728_1760
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1728_1760 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 16 r := by sorry
