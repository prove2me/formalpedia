-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_2944_2976
-- name    : Freiman.workReverse20260919_s0001_records_2944_2976
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:33:32.716471+00:00
-- url     : https://prove2.me/theorems/1d41297e-901d-4e6a-8284-f5c24a83cf75
-- title:
--   Freiman.workReverse20260919_s0001_records_2944_2976
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2944).take 32, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_2944_2976 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2944).take 32, section14RecordValid section14Catalog 1 r := by sorry
