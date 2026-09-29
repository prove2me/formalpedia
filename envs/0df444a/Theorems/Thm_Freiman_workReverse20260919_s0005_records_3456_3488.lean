-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3456_3488
-- name    : Freiman.workReverse20260919_s0005_records_3456_3488
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:09:04.396392+00:00
-- url     : https://prove2.me/theorems/b104fb87-3164-49e4-9d5c-ce0c6dea47b4
-- title:
--   Freiman.workReverse20260919_s0005_records_3456_3488
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3456).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3456_3488 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3456).take 32, section14RecordValid section14Catalog 5 r := by sorry
