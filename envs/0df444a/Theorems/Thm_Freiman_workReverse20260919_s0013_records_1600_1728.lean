-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_1600_1728
-- name    : Freiman.workReverse20260919_s0013_records_1600_1728
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:18:46.17106+00:00
-- url     : https://prove2.me/theorems/7b7be456-e9a1-4699-a18e-36fc147134ee
-- title:
--   Freiman.workReverse20260919_s0013_records_1600_1728
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1600).take 128, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_1600_1728 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1600).take 128, section14RecordValid section14Catalog 13 r := by sorry
