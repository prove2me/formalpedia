-- Prove2me | Theorems.Thm_Freiman_section14_s0004_records_0352_0384
-- name    : Freiman.section14_s0004_records_0352_0384
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T02:06:28.707814+00:00
-- url     : https://prove2.me/theorems/29a0f559-71e2-4c34-8569-8626180daeca
-- title:
--   Freiman.section14_s0004_records_0352_0384
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 4 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_records_0352_0384 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 4 r := by sorry
