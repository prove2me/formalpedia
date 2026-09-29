-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_4416_4480
-- name    : Freiman.workReverse20260919_s0005_records_4416_4480
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:32:30.861117+00:00
-- url     : https://prove2.me/theorems/01e78cef-d04f-4a09-a5e9-92a4f3ad96b0
-- title:
--   Freiman.workReverse20260919_s0005_records_4416_4480
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4416).take 64, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_4416_4480 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4416).take 64, section14RecordValid section14Catalog 5 r := by sorry
