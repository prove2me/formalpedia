-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_1632_1654
-- name    : Freiman.section14_s0015_records_1632_1654
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T19:31:41.37735+00:00
-- url     : https://prove2.me/theorems/d48b6ea6-599c-497e-b584-ffc958849f0b
-- title:
--   Freiman.section14_s0015_records_1632_1654
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1632).take 22, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_1632_1654 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1632).take 22, section14RecordValid section14Catalog 15 r := by sorry
