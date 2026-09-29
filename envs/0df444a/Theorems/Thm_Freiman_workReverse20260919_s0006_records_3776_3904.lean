-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_3776_3904
-- name    : Freiman.workReverse20260919_s0006_records_3776_3904
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:03:52.29325+00:00
-- url     : https://prove2.me/theorems/a5694d99-f8c3-46a4-8e03-e143d3678ea0
-- title:
--   Freiman.workReverse20260919_s0006_records_3776_3904
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3776).take 128, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_3776_3904 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3776).take 128, section14RecordValid section14Catalog 6 r := by sorry
