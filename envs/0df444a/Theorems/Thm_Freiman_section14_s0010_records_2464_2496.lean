-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_2464_2496
-- name    : Freiman.section14_s0010_records_2464_2496
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T18:04:29.050395+00:00
-- url     : https://prove2.me/theorems/76980ab4-1d48-4e08-b42e-d0aac010a6b8
-- title:
--   Freiman.section14_s0010_records_2464_2496
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_2464_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 10 r := by sorry
