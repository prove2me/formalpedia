-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_1152_1184
-- name    : Freiman.section14_s0016_records_1152_1184
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T23:21:39.759392+00:00
-- url     : https://prove2.me/theorems/b8d6cc67-6315-4ed6-bb81-7e155510193f
-- title:
--   Freiman.section14_s0016_records_1152_1184
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_1152_1184 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 16 r := by sorry
