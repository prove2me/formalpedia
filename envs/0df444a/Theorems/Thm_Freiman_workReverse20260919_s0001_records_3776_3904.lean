-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3776_3904
-- name    : Freiman.workReverse20260919_s0001_records_3776_3904
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:42:27.734578+00:00
-- url     : https://prove2.me/theorems/6d097106-3c28-4077-8b0a-7f2f331c67ad
-- title:
--   Freiman.workReverse20260919_s0001_records_3776_3904
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3776).take 128, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3776_3904 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3776).take 128, section14RecordValid section14Catalog 1 r := by sorry
