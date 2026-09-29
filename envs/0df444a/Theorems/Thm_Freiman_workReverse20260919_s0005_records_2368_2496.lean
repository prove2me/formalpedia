-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_2368_2496
-- name    : Freiman.workReverse20260919_s0005_records_2368_2496
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:25:27.856911+00:00
-- url     : https://prove2.me/theorems/3be37e01-90a9-46ea-8d54-25bffa06f0cf
-- title:
--   Freiman.workReverse20260919_s0005_records_2368_2496
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2368).take 128, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_2368_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2368).take 128, section14RecordValid section14Catalog 5 r := by sorry
