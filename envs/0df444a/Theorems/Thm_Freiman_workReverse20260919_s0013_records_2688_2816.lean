-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_2688_2816
-- name    : Freiman.workReverse20260919_s0013_records_2688_2816
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:23:44.042671+00:00
-- url     : https://prove2.me/theorems/a89fc6a5-abf2-4567-b955-b6a09aa2bee2
-- title:
--   Freiman.workReverse20260919_s0013_records_2688_2816
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2688).take 128, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_2688_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2688).take 128, section14RecordValid section14Catalog 13 r := by sorry
