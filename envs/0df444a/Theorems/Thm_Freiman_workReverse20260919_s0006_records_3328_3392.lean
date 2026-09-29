-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_3328_3392
-- name    : Freiman.workReverse20260919_s0006_records_3328_3392
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:51:28.750404+00:00
-- url     : https://prove2.me/theorems/78054cdf-8d2f-4faf-8b1c-6d631755da58
-- title:
--   Freiman.workReverse20260919_s0006_records_3328_3392
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3328).take 64, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_3328_3392 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3328).take 64, section14RecordValid section14Catalog 6 r := by sorry
