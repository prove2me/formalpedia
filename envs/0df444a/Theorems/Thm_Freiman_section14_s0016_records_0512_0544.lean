-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0512_0544
-- name    : Freiman.section14_s0016_records_0512_0544
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:53:23.51137+00:00
-- url     : https://prove2.me/theorems/dabec85a-2a34-45b3-aa09-f2d87c4ede9f
-- title:
--   Freiman.section14_s0016_records_0512_0544
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0512_0544 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 16 r := by sorry
