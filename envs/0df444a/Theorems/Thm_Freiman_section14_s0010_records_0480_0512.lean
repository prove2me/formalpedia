-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0480_0512
-- name    : Freiman.section14_s0010_records_0480_0512
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:40:33.979993+00:00
-- url     : https://prove2.me/theorems/35679c41-481c-426d-ae8b-3e689de51c7e
-- title:
--   Freiman.section14_s0010_records_0480_0512
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0480_0512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 10 r := by sorry
