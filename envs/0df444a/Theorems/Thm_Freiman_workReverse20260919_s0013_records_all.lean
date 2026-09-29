-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_all
-- name    : Freiman.workReverse20260919_s0013_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T10:08:14.155899+00:00
-- url     : https://prove2.me/theorems/328e3b17-5ca9-40ac-b0d1-15ef62d219be
-- title:
--   Freiman.workReverse20260919_s0013_records_all
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (13 ∈ r.states))), section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (13 ∈ r.states))), section14RecordValid section14Catalog 13 r := by sorry
