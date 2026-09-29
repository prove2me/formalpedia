-- Prove2me | Theorems.Thm_Freiman_section14_s0009_records_0576_0608
-- name    : Freiman.section14_s0009_records_0576_0608
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T20:09:38.467189+00:00
-- url     : https://prove2.me/theorems/4f2ec2b2-3119-4e31-996c-b3f89deb331f
-- title:
--   Freiman.section14_s0009_records_0576_0608
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 9 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 9 r := by sorry
