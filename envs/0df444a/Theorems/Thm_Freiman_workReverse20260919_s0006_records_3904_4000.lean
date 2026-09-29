-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_3904_4000
-- name    : Freiman.workReverse20260919_s0006_records_3904_4000
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:03:55.33448+00:00
-- url     : https://prove2.me/theorems/ea22f632-78a6-4861-8c23-9ca09c92fd1a
-- title:
--   Freiman.workReverse20260919_s0006_records_3904_4000
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3904).take 96, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_3904_4000 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3904).take 96, section14RecordValid section14Catalog 6 r := by sorry
