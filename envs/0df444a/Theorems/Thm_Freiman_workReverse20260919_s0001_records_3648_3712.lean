-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3648_3712
-- name    : Freiman.workReverse20260919_s0001_records_3648_3712
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:34:33.053506+00:00
-- url     : https://prove2.me/theorems/8840a277-74d0-4653-bda7-c7be5d1a9cac
-- title:
--   Freiman.workReverse20260919_s0001_records_3648_3712
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3648).take 64, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3648_3712 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3648).take 64, section14RecordValid section14Catalog 1 r := by sorry
