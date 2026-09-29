-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_0608_0640
-- name    : Freiman.section14_s0009_records_0608_0640
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:10:19.143243+00:00
-- url     : https://prove2.me/theorems/77e705ba-7ab2-4c7e-9027-71f0ca41630a
-- title:
--   Freiman.section14_s0009_records_0608_0640
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 9 r := by sorry
