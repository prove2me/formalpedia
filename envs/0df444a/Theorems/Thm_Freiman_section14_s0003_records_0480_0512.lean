-- Prove2me | Theorems.Thm_Freiman_section14_s0003_records_0480_0512
-- name    : Freiman.section14_s0003_records_0480_0512
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T12:27:26.621637+00:00
-- url     : https://prove2.me/theorems/78f10f69-de20-4c36-a47d-3f7a792d11bb
-- title:
--   Freiman.section14_s0003_records_0480_0512
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 3 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0003_records_0480_0512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 3 r := by sorry
