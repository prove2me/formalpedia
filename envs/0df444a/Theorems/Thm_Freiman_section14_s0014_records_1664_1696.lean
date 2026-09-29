-- Prove2me | Theorems.Thm_Freiman_section14_s0014_records_1664_1696
-- name    : Freiman.section14_s0014_records_1664_1696
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T02:16:18.875987+00:00
-- url     : https://prove2.me/theorems/4998fd78-4eb9-415e-b4ce-b14320ddd0fe
-- title:
--   Freiman.section14_s0014_records_1664_1696
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 14 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_records_1664_1696 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 14 r := by sorry
