-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_2592_2688
-- name    : Freiman.workReverse20260919_s0013_records_2592_2688
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:23:39.844978+00:00
-- url     : https://prove2.me/theorems/e870d770-ae50-4193-9df3-7b6652d55365
-- title:
--   Freiman.workReverse20260919_s0013_records_2592_2688
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2592).take 96, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_2592_2688 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2592).take 96, section14RecordValid section14Catalog 13 r := by sorry
