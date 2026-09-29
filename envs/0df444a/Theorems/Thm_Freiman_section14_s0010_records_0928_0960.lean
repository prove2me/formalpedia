-- Prove2me | Theorems.Thm_Freiman_section14_s0010_records_0928_0960
-- name    : Freiman.section14_s0010_records_0928_0960
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T16:53:39.89185+00:00
-- url     : https://prove2.me/theorems/05cb4e1d-0d78-43bf-b96c-e0405b979887
-- title:
--   Freiman.section14_s0010_records_0928_0960
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 10 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0010_records_0928_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 10 r := by sorry
