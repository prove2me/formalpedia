-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_3616_3648
-- name    : Freiman.workReverse20260919_s0005_records_3616_3648
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:02:10.720546+00:00
-- url     : https://prove2.me/theorems/3f11225e-8893-4691-9a70-55123a96d153
-- title:
--   Freiman.workReverse20260919_s0005_records_3616_3648
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3616).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_3616_3648 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3616).take 32, section14RecordValid section14Catalog 5 r := by sorry
