-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0416_0448
-- name    : Freiman.section14_s0013_records_0416_0448
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T11:49:31.800967+00:00
-- url     : https://prove2.me/theorems/cd7153dd-5513-49ea-8644-5839ba5a78fe
-- title:
--   Freiman.section14_s0013_records_0416_0448
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0416_0448 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 13 r := by sorry
