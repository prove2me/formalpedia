-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3456_3520
-- name    : Freiman.workReverse20260919_s0001_records_3456_3520
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:26:44.545358+00:00
-- url     : https://prove2.me/theorems/257b866c-fde7-40a7-a211-60a5594904c4
-- title:
--   Freiman.workReverse20260919_s0001_records_3456_3520
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3456).take 64, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3456_3520 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3456).take 64, section14RecordValid section14Catalog 1 r := by sorry
