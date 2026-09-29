-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_2592_2624
-- name    : Freiman.workReverse20260919_s0013_records_2592_2624
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:21:27.768916+00:00
-- url     : https://prove2.me/theorems/4fa4a67e-1606-4a8e-a76e-c519862bd943
-- title:
--   Freiman.workReverse20260919_s0013_records_2592_2624
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 13 r := by sorry
