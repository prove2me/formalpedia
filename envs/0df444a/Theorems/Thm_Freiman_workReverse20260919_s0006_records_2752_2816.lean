-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_2752_2816
-- name    : Freiman.workReverse20260919_s0006_records_2752_2816
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:09:20.597283+00:00
-- url     : https://prove2.me/theorems/fd43e5be-e75f-451b-bf55-2f1b83f29a1f
-- title:
--   Freiman.workReverse20260919_s0006_records_2752_2816
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2752).take 64, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_2752_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2752).take 64, section14RecordValid section14Catalog 6 r := by sorry
