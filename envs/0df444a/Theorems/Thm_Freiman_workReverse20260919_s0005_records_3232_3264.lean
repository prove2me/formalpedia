-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3232_3264
-- name    : Freiman.workReverse20260919_s0005_records_3232_3264
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:53:10.195166+00:00
-- url     : https://prove2.me/theorems/f6b232f0-ef91-492c-941f-1db397b900f8
-- title:
--   Freiman.workReverse20260919_s0005_records_3232_3264
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3232).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3232_3264 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3232).take 32, section14RecordValid section14Catalog 5 r := by sorry
