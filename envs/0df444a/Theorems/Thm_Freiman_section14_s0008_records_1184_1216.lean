-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_1184_1216
-- name    : Freiman.section14_s0008_records_1184_1216
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:19:39.367284+00:00
-- url     : https://prove2.me/theorems/51a8736e-6b9e-442d-989e-89f156477021
-- title:
--   Freiman.section14_s0008_records_1184_1216
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 8 r := by sorry
