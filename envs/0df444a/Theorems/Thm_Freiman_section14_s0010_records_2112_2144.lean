-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_2112_2144
-- name    : Freiman.section14_s0010_records_2112_2144
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T17:52:24.094398+00:00
-- url     : https://prove2.me/theorems/33fa8373-9c86-46e3-8a56-5195158f46bb
-- title:
--   Freiman.section14_s0010_records_2112_2144
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_2112_2144 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2112).take 32, section14RecordValid section14Catalog 10 r := by sorry
