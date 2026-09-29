-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1408_1536
-- name    : Freiman.section14_pairWitnesses_1408_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:39:14.61998+00:00
-- url     : https://prove2.me/theorems/46b7fe52-287d-43f0-a607-17bb989cc37e
-- title:
--   Freiman.section14_pairWitnesses_1408_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1408).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1408_1536 : ∀ a ∈ (section14Catalog.assignments.drop 1408).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
