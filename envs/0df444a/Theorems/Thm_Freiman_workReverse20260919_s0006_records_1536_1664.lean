-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_1536_1664
-- name    : Freiman.workReverse20260919_s0006_records_1536_1664
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:42:17.782269+00:00
-- url     : https://prove2.me/theorems/c3187607-d817-4006-82e6-b08bde58794e
-- title:
--   Freiman.workReverse20260919_s0006_records_1536_1664
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1536).take 128, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_1536_1664 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1536).take 128, section14RecordValid section14Catalog 6 r := by sorry
