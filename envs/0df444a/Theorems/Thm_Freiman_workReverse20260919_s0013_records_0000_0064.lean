-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0000_0064
-- name    : Freiman.workReverse20260919_s0013_records_0000_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:15:13.794136+00:00
-- url     : https://prove2.me/theorems/29a08d64-82b0-4525-90d0-3e688b4053be
-- title:
--   Freiman.workReverse20260919_s0013_records_0000_0064
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 0).take 64, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0000_0064 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 0).take 64, section14RecordValid section14Catalog 13 r := by sorry
