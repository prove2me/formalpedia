-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_0224_0256
-- name    : Freiman.section14_s0015_records_0224_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T17:45:51.212361+00:00
-- url     : https://prove2.me/theorems/c10c1e19-25bc-4fcc-8d93-9c9c453a3aec
-- title:
--   Freiman.section14_s0015_records_0224_0256
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_0224_0256 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 224).take 32, section14RecordValid section14Catalog 15 r := by sorry
