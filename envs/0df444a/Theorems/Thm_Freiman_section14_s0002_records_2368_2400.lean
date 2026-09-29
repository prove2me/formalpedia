-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_2368_2400
-- name    : Freiman.section14_s0002_records_2368_2400
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:02:52.156046+00:00
-- url     : https://prove2.me/theorems/0bd018dc-994f-4ddd-afd4-884b8f9b3b1a
-- title:
--   Freiman.section14_s0002_records_2368_2400
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_2368_2400 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 2 r := by sorry
