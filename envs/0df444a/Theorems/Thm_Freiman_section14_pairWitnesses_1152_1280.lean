-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1152_1280
-- name    : Freiman.section14_pairWitnesses_1152_1280
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:23:57.283765+00:00
-- url     : https://prove2.me/theorems/2e136a0e-55b1-4383-a276-abc1f9dfd3a6
-- title:
--   Freiman.section14_pairWitnesses_1152_1280
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1152).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1152_1280 : ∀ a ∈ (section14Catalog.assignments.drop 1152).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
