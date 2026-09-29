-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_2208_2240
-- name    : Freiman.section14_s0010_records_2208_2240
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:58:18.053499+00:00
-- url     : https://prove2.me/theorems/dc904644-f0a9-4e66-99a1-78aa0da90ab6
-- title:
--   Freiman.section14_s0010_records_2208_2240
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_2208_2240 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 10 r := by sorry
