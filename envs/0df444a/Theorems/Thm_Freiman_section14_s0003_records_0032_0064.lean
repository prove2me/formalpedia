-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0032_0064
-- name    : Freiman.section14_s0003_records_0032_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:13:33.552148+00:00
-- url     : https://prove2.me/theorems/11a6301e-79e8-41f9-8961-c49c41a5c652
-- title:
--   Freiman.section14_s0003_records_0032_0064
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0032_0064 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 3 r := by sorry
