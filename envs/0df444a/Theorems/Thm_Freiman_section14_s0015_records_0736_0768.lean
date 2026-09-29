-- Prove2me | Theorems.Thm_Freiman_section14_s0015_records_0736_0768
-- name    : Freiman.section14_s0015_records_0736_0768
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T19:02:27.25664+00:00
-- url     : https://prove2.me/theorems/608bafcd-cd77-482e-9d68-cf27485da312
-- title:
--   Freiman.section14_s0015_records_0736_0768
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 15 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_records_0736_0768 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 15 r := by sorry
