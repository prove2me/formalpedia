-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0864_0896
-- name    : Freiman.section14_s0007_records_0864_0896
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:41:26.096367+00:00
-- url     : https://prove2.me/theorems/ce19afdd-419d-44a3-9b5a-dd2b53e4bf93
-- title:
--   Freiman.section14_s0007_records_0864_0896
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0864_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 7 r := by sorry
