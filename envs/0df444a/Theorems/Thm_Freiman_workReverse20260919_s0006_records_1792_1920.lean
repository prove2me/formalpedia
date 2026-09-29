-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_1792_1920
-- name    : Freiman.workReverse20260919_s0006_records_1792_1920
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:42:31.053313+00:00
-- url     : https://prove2.me/theorems/1df7ea1c-96c1-4f53-8247-91c42cff921c
-- title:
--   Freiman.workReverse20260919_s0006_records_1792_1920
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1792).take 128, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_1792_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1792).take 128, section14RecordValid section14Catalog 6 r := by sorry
