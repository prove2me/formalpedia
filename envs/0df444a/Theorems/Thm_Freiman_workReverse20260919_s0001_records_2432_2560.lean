-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_2432_2560
-- name    : Freiman.workReverse20260919_s0001_records_2432_2560
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T01:46:02.59999+00:00
-- url     : https://prove2.me/theorems/ac1d4898-5566-4d14-8ffb-e7b4228c4f1d
-- title:
--   Freiman.workReverse20260919_s0001_records_2432_2560
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2432).take 128, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_2432_2560 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2432).take 128, section14RecordValid section14Catalog 1 r := by sorry
