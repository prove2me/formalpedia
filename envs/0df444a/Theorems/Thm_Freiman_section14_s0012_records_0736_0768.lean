-- Prove2me | Theorems.Thm_Freiman_section14_s0012_records_0736_0768
-- name    : Freiman.section14_s0012_records_0736_0768
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T04:35:53.114981+00:00
-- url     : https://prove2.me/theorems/6c933e34-9b50-4aa7-9803-c344185929e1
-- title:
--   Freiman.section14_s0012_records_0736_0768
-- statement:
--   Exact auxiliary assertion from Freiman section 14. (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 12 r
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0012_records_0736_0768 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 12 r := by sorry
