-- Prove2me | Theorems.Thm_Freiman_section14_s0002_records_0032_0064
-- name    : Freiman.section14_s0002_records_0032_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:50:30.393982+00:00
-- url     : https://prove2.me/theorems/40c3f725-da29-44bc-901f-0227827709f5
-- title:
--   Freiman.section14_s0002_records_0032_0064
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 2 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0002_records_0032_0064 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 32).take 32, section14RecordValid section14Catalog 2 r := by sorry
