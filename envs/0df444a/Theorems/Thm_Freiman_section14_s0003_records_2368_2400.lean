-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_2368_2400
-- name    : Freiman.section14_s0003_records_2368_2400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:42:06.246366+00:00
-- url     : https://prove2.me/theorems/7d758a92-ab37-49af-8d6b-7f004bf4fc99
-- title:
--   Freiman.section14_s0003_records_2368_2400
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_2368_2400 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 3 r := by sorry
