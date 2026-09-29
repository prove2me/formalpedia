-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0013_records_2144_2176
-- name    : Freiman.workReverse20260919_s0013_records_2144_2176
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T09:19:10.578765+00:00
-- url     : https://prove2.me/theorems/0348b750-2530-4cf6-84d9-fdd21702149b
-- title:
--   Freiman.workReverse20260919_s0013_records_2144_2176
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0013_records_2144_2176 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 13 r := by sorry
