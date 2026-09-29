-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_records_2112_2144
-- name    : Freiman.workReverse20260919_s0006_records_2112_2144
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:31:20.043961+00:00
-- url     : https://prove2.me/theorems/a4648f38-e627-48d5-92ff-edb4d0982379
-- title:
--   Freiman.workReverse20260919_s0006_records_2112_2144
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 6 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_records_2112_2144 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 6 r := by sorry
