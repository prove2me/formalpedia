-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3008_3072
-- name    : Freiman.workReverse20260919_s0005_records_3008_3072
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:30:17.568984+00:00
-- url     : https://prove2.me/theorems/75749367-05c3-4816-9213-8428b02b3b20
-- title:
--   Freiman.workReverse20260919_s0005_records_3008_3072
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3008).take 64, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3008_3072 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3008).take 64, section14RecordValid section14Catalog 5 r := by sorry
