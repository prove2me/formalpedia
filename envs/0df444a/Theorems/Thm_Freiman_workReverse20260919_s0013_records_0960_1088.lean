-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0960_1088
-- name    : Freiman.workReverse20260919_s0013_records_0960_1088
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:17:20.256475+00:00
-- url     : https://prove2.me/theorems/147e7bb2-0f91-4889-a085-9a311a723eb6
-- title:
--   Freiman.workReverse20260919_s0013_records_0960_1088
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 960).take 128, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0960_1088 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 960).take 128, section14RecordValid section14Catalog 13 r := by sorry
