-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_1888_1920
-- name    : Freiman.workReverse20260919_s0013_records_1888_1920
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:15:30.659158+00:00
-- url     : https://prove2.me/theorems/1655d60c-24c2-45f0-a076-3c1a1b62b5f1
-- title:
--   Freiman.workReverse20260919_s0013_records_1888_1920
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_1888_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 13 r := by sorry
