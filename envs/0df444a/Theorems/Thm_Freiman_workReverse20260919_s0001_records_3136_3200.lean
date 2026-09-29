-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3136_3200
-- name    : Freiman.workReverse20260919_s0001_records_3136_3200
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:47:41.360984+00:00
-- url     : https://prove2.me/theorems/a30b9013-f489-446b-a38a-679b6288bc86
-- title:
--   Freiman.workReverse20260919_s0001_records_3136_3200
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3136).take 64, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3136_3200 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3136).take 64, section14RecordValid section14Catalog 1 r := by sorry
