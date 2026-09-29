-- Prove2me | Theorems.Thm_Freiman_section14_s0011_records_1120_1184
-- name    : Freiman.section14_s0011_records_1120_1184
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T12:49:42.178804+00:00
-- url     : https://prove2.me/theorems/35040074-f61c-46ab-b66b-5b99df92ee67
-- title:
--   Freiman.section14_s0011_records_1120_1184
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1120).take 64, section14RecordValid section14Catalog 11 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_records_1120_1184 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1120).take 64, section14RecordValid section14Catalog 11 r := by sorry
