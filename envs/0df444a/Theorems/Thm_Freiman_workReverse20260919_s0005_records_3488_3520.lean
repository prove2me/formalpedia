-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3488_3520
-- name    : Freiman.workReverse20260919_s0005_records_3488_3520
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:59:12.701002+00:00
-- url     : https://prove2.me/theorems/8fdd848a-be30-46fa-8091-8ef9bbe4c26f
-- title:
--   Freiman.workReverse20260919_s0005_records_3488_3520
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3488).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3488_3520 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3488).take 32, section14RecordValid section14Catalog 5 r := by sorry
