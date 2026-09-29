-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_1664_1696
-- name    : Freiman.section14_s0010_records_1664_1696
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:15:58.131981+00:00
-- url     : https://prove2.me/theorems/df17e282-8ff0-44eb-8c58-962a6214a636
-- title:
--   Freiman.section14_s0010_records_1664_1696
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_1664_1696 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 10 r := by sorry
