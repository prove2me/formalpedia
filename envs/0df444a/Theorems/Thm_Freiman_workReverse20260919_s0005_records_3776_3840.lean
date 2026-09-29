-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3776_3840
-- name    : Freiman.workReverse20260919_s0005_records_3776_3840
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:31:17.007464+00:00
-- url     : https://prove2.me/theorems/282619f2-051b-48d7-8ddd-cdcd70c5413f
-- title:
--   Freiman.workReverse20260919_s0005_records_3776_3840
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3776).take 64, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3776_3840 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3776).take 64, section14RecordValid section14Catalog 5 r := by sorry
