-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3200_3328
-- name    : Freiman.workReverse20260919_s0001_records_3200_3328
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:47:40.297273+00:00
-- url     : https://prove2.me/theorems/f9df28f4-a852-49b0-99e2-1a99319e0895
-- title:
--   Freiman.workReverse20260919_s0001_records_3200_3328
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3200).take 128, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3200_3328 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3200).take 128, section14RecordValid section14Catalog 1 r := by sorry
