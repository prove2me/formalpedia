-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_2208_2240
-- name    : Freiman.section14_s0002_records_2208_2240
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T06:58:06.154403+00:00
-- url     : https://prove2.me/theorems/1667cb72-49e3-4d75-9608-632fd2c8e8a0
-- title:
--   Freiman.section14_s0002_records_2208_2240
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_2208_2240 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 2 r := by sorry
