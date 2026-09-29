-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1280_1408
-- name    : Freiman.section14_pairWitnesses_1280_1408
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:36:19.226328+00:00
-- url     : https://prove2.me/theorems/cc1c9b13-24bf-4a66-8972-dfdc41ae9bb2
-- title:
--   Freiman.section14_pairWitnesses_1280_1408
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1280).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1280_1408 : ∀ a ∈ (section14Catalog.assignments.drop 1280).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
