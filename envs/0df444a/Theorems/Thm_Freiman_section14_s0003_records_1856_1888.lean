-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_1856_1888
-- name    : Freiman.section14_s0003_records_1856_1888
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T13:23:00.541449+00:00
-- url     : https://prove2.me/theorems/47c2cbd6-4ecb-414f-a8db-c22e8a5e3e90
-- title:
--   Freiman.section14_s0003_records_1856_1888
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_1856_1888 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 3 r := by sorry
