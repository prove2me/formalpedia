-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_2464_2496
-- name    : Freiman.section14_s0002_records_2464_2496
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:08:19.46937+00:00
-- url     : https://prove2.me/theorems/5b50034c-b8d4-4f4b-a64c-114b296c479b
-- title:
--   Freiman.section14_s0002_records_2464_2496
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_2464_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 2 r := by sorry
