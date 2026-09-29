-- Prove2me | Theorems.Thm_Freiman_section14_s0008_records_0608_0640
-- name    : Freiman.section14_s0008_records_0608_0640
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T07:03:15.728959+00:00
-- url     : https://prove2.me/theorems/009c8205-e4b8-4852-a478-0b74569b283d
-- title:
--   Freiman.section14_s0008_records_0608_0640
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 8 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 8 r := by sorry
