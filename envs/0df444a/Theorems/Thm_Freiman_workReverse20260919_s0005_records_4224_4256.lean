-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_records_4224_4256
-- name    : Freiman.workReverse20260919_s0005_records_4224_4256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T08:04:23.351645+00:00
-- url     : https://prove2.me/theorems/6c74b6c1-384b-4a5c-a57f-5781d77dbdaf
-- title:
--   Freiman.workReverse20260919_s0005_records_4224_4256
-- statement:
--   Each selected original record is checked with an explicit original assignment, exact premise bounds, branch conditions and rectangle. The separately stated numerical witness hypothesis supplies precisely the missing numerical conjunct. All records in the indicated filtered catalogue slice are included.
--
--   (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4224).take 32, section14RecordValid section14Catalog 5 r
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_records_4224_4256 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4224).take 32, section14RecordValid section14Catalog 5 r := by sorry
