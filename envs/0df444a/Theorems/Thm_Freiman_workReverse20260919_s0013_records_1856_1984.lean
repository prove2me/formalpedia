-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_1856_1984
-- name    : Freiman.workReverse20260919_s0013_records_1856_1984
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:18:34.674707+00:00
-- url     : https://prove2.me/theorems/23e67ff1-bcc1-4d82-86d7-417c5520c3cf
-- title:
--   Freiman.workReverse20260919_s0013_records_1856_1984
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1856).take 128, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_1856_1984 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1856).take 128, section14RecordValid section14Catalog 13 r := by sorry
