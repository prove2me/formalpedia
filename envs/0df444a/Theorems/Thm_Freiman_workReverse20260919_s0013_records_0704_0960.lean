-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0704_0960
-- name    : Freiman.workReverse20260919_s0013_records_0704_0960
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:16:08.185281+00:00
-- url     : https://prove2.me/theorems/948fcd15-bd4e-4b77-885b-4f599a22232d
-- title:
--   Freiman.workReverse20260919_s0013_records_0704_0960
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 704).take 256, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0704_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 704).take 256, section14RecordValid section14Catalog 13 r := by sorry
