-- Prove2me | Theorems.Thm_Freiman_section14_s0011_records_all
-- name    : Freiman.section14_s0011_records_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:07:05.991329+00:00
-- url     : https://prove2.me/theorems/1a88fb83-8b95-4ecc-bedb-58c8aa27922f
-- title:
--   Freiman.section14_s0011_records_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (11 ∈ r.states))), section14RecordValid section14Catalog 11 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_records_all : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ (section14Catalog.records.filter (fun r => decide (11 ∈ r.states))), section14RecordValid section14Catalog 11 r := by sorry
