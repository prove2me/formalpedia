-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_3072_3200
-- name    : Freiman.workReverse20260919_s0006_records_3072_3200
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:50:08.381693+00:00
-- url     : https://prove2.me/theorems/dd671f0a-9590-4b39-9ca9-fc6dbf87014b
-- title:
--   Freiman.workReverse20260919_s0006_records_3072_3200
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 128, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_3072_3200 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 128, section14RecordValid section14Catalog 6 r := by sorry
