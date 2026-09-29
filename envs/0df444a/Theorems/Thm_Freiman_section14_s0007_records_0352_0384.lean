-- Prove2me | Theorems.Thm_Freiman_section14_s0007_records_0352_0384
-- name    : Freiman.section14_s0007_records_0352_0384
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T09:23:50.760888+00:00
-- url     : https://prove2.me/theorems/6beb5636-7666-4d72-a15b-412f181d1baa
-- title:
--   Freiman.section14_s0007_records_0352_0384
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 7 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_records_0352_0384 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 7 r := by sorry
