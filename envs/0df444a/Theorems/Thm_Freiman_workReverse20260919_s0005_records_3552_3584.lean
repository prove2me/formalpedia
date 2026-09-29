-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3552_3584
-- name    : Freiman.workReverse20260919_s0005_records_3552_3584
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:01:23.726911+00:00
-- url     : https://prove2.me/theorems/e3c797d6-f607-4ca0-acf4-5f8894524a2c
-- title:
--   Freiman.workReverse20260919_s0005_records_3552_3584
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3552).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3552_3584 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3552).take 32, section14RecordValid section14Catalog 5 r := by sorry
