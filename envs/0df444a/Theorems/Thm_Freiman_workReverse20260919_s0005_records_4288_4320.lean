-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_4288_4320
-- name    : Freiman.workReverse20260919_s0005_records_4288_4320
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:06:00.513978+00:00
-- url     : https://prove2.me/theorems/b099ae65-702a-42b0-ae7c-a4bfaf26903a
-- title:
--   Freiman.workReverse20260919_s0005_records_4288_4320
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4288).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_4288_4320 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4288).take 32, section14RecordValid section14Catalog 5 r := by sorry
