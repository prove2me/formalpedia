-- Prove2me | Theorems.Thm_Freiman_section14_s0016_records_0256_0288
-- name    : Freiman.section14_s0016_records_0256_0288
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T22:42:19.866646+00:00
-- url     : https://prove2.me/theorems/08f434cd-153f-4595-b9ad-fc879dea34df
-- title:
--   Freiman.section14_s0016_records_0256_0288
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 16 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_records_0256_0288 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 256).take 32, section14RecordValid section14Catalog 16 r := by sorry
