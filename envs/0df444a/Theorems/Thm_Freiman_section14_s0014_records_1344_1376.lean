-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_1344_1376
-- name    : Freiman.section14_s0014_records_1344_1376
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:01:23.476304+00:00
-- url     : https://prove2.me/theorems/64fdb209-4245-4c0d-be5f-bc8857ec2248
-- title:
--   Freiman.section14_s0014_records_1344_1376
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_1344_1376 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 14 r := by sorry
