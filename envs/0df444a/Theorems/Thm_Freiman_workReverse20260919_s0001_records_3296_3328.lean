-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_records_3296_3328
-- name    : Freiman.workReverse20260919_s0001_records_3296_3328
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:08:56.66502+00:00
-- url     : https://prove2.me/theorems/93a441b6-3a85-4e4c-ba1a-1bbee51a318e
-- title:
--   Freiman.workReverse20260919_s0001_records_3296_3328
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3296).take 32, section14RecordValid section14Catalog 1 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_records_3296_3328 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3296).take 32, section14RecordValid section14Catalog 1 r := by sorry
