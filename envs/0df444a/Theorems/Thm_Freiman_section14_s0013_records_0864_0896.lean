-- Prove2me | Theorems.Thm_Freiman_section14_s0013_records_0864_0896
-- name    : Freiman.section14_s0013_records_0864_0896
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T12:02:09.127605+00:00
-- url     : https://prove2.me/theorems/46f0ecf7-baca-41a9-a165-d5f797ae4411
-- title:
--   Freiman.section14_s0013_records_0864_0896
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 13 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0013_records_0864_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 13 r := by sorry
