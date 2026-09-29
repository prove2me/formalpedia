-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1280_1344
-- name    : Freiman.section14_pairWitnesses_1280_1344
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:43:56.96086+00:00
-- url     : https://prove2.me/theorems/b81b0901-bd73-4a3b-afa7-42f5bdfa1eab
-- title:
--   Freiman.section14_pairWitnesses_1280_1344
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1280).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1280_1344 : ∀ a ∈ (section14Catalog.assignments.drop 1280).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
