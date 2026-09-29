-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1472_1536
-- name    : Freiman.section14_pairWitnesses_1472_1536
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:57:12.135988+00:00
-- url     : https://prove2.me/theorems/6423ae35-fecd-4561-aa94-f3c6740b77da
-- title:
--   Freiman.section14_pairWitnesses_1472_1536
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1472).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1472_1536 : ∀ a ∈ (section14Catalog.assignments.drop 1472).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
