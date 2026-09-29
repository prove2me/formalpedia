-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_3072_3104
-- name    : Freiman.workReverse20260919_s0006_records_3072_3104
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:42:40.949354+00:00
-- url     : https://prove2.me/theorems/2a5066e5-e0f4-48a8-8c85-988ed978343f
-- title:
--   Freiman.workReverse20260919_s0006_records_3072_3104
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 32, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_3072_3104 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 32, section14RecordValid section14Catalog 6 r := by sorry
