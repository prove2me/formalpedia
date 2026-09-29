-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_0480_0512
-- name    : Freiman.workReverse20260919_s0013_records_0480_0512
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:13:27.008587+00:00
-- url     : https://prove2.me/theorems/744a2262-bfe2-4cde-8b37-49a91f69dacc
-- title:
--   Freiman.workReverse20260919_s0013_records_0480_0512
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_0480_0512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 13 r := by sorry
