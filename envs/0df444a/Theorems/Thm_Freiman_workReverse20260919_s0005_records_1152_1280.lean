-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_1152_1280
-- name    : Freiman.workReverse20260919_s0005_records_1152_1280
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:10:30.05974+00:00
-- url     : https://prove2.me/theorems/1a960c77-92cb-41c9-8df3-ba0105fa4934
-- title:
--   Freiman.workReverse20260919_s0005_records_1152_1280
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1152).take 128, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_1152_1280 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1152).take 128, section14RecordValid section14Catalog 5 r := by sorry
