-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_0256_0384
-- name    : Freiman.section14_pairWitnesses_0256_0384
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:05:34.564196+00:00
-- url     : https://prove2.me/theorems/2fba93e4-5dd4-4a82-8c3f-b4ffc05b5a71
-- title:
--   Freiman.section14_pairWitnesses_0256_0384
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 256).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_0256_0384 : ∀ a ∈ (section14Catalog.assignments.drop 256).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
