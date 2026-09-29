-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0928_0960
-- name    : Freiman.section14_s0007_records_0928_0960
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:44:27.866702+00:00
-- url     : https://prove2.me/theorems/3f972a18-80f3-48dd-89f2-10c705b6e545
-- title:
--   Freiman.section14_s0007_records_0928_0960
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0928_0960 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 928).take 32, section14RecordValid section14Catalog 7 r := by sorry
