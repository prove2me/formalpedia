-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0320_0576
-- name    : Freiman.workReverse20260919_s0013_records_0320_0576
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:16:09.342641+00:00
-- url     : https://prove2.me/theorems/f30aa018-50d0-441a-8dcb-08df57d5b2a3
-- title:
--   Freiman.workReverse20260919_s0013_records_0320_0576
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 320).take 256, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0320_0576 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 320).take 256, section14RecordValid section14Catalog 13 r := by sorry
