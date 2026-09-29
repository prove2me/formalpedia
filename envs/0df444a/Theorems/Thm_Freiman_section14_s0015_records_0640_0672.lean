-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_0640_0672
-- name    : Freiman.section14_s0015_records_0640_0672
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T18:58:51.734848+00:00
-- url     : https://prove2.me/theorems/047b1bb0-36fc-4505-9720-191616665c95
-- title:
--   Freiman.section14_s0015_records_0640_0672
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 640).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_0640_0672 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 640).take 32, section14RecordValid section14Catalog 15 r := by sorry
