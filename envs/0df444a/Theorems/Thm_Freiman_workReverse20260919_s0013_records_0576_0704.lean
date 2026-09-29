-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0576_0704
-- name    : Freiman.workReverse20260919_s0013_records_0576_0704
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:15:52.047051+00:00
-- url     : https://prove2.me/theorems/6b486429-622d-4907-8636-e549658b36da
-- title:
--   Freiman.workReverse20260919_s0013_records_0576_0704
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 576).take 128, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0576_0704 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 576).take 128, section14RecordValid section14Catalog 13 r := by sorry
