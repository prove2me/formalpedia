-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0480_0512
-- name    : Freiman.section14_s0008_records_0480_0512
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:58:18.645992+00:00
-- url     : https://prove2.me/theorems/0082b7a1-5b0d-4461-ae32-88cb2f4e5a4f
-- title:
--   Freiman.section14_s0008_records_0480_0512
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0480_0512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 8 r := by sorry
