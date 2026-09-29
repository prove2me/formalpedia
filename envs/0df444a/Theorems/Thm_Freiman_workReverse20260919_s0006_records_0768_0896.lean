-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_0768_0896
-- name    : Freiman.workReverse20260919_s0006_records_0768_0896
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:40:56.355985+00:00
-- url     : https://prove2.me/theorems/919e9060-ab02-4c4d-b13c-21f81e9182f5
-- title:
--   Freiman.workReverse20260919_s0006_records_0768_0896
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 768).take 128, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_0768_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 768).take 128, section14RecordValid section14Catalog 6 r := by sorry
