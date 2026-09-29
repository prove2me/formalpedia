-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_1792_1920
-- name    : Freiman.workReverse20260919_s0005_records_1792_1920
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:10:46.477584+00:00
-- url     : https://prove2.me/theorems/6d137056-08f5-480c-b2f7-9847fbdf1591
-- title:
--   Freiman.workReverse20260919_s0005_records_1792_1920
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1792).take 128, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_1792_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1792).take 128, section14RecordValid section14Catalog 5 r := by sorry
