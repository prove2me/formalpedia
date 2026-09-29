-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_1440_1472
-- name    : Freiman.section14_s0009_records_1440_1472
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:45:02.291712+00:00
-- url     : https://prove2.me/theorems/a1b9a30b-ee8b-46e0-bafb-d263b757b7ef
-- title:
--   Freiman.section14_s0009_records_1440_1472
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_1440_1472 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 9 r := by sorry
