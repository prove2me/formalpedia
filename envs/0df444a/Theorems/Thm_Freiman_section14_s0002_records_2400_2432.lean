-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_2400_2432
-- name    : Freiman.section14_s0002_records_2400_2432
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:04:51.089737+00:00
-- url     : https://prove2.me/theorems/cd6918da-61d1-40a7-bbef-8fc2d12f0a2e
-- title:
--   Freiman.section14_s0002_records_2400_2432
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_2400_2432 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 2 r := by sorry
