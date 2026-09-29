-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_0128_0256
-- name    : Freiman.section14_pairWitnesses_0128_0256
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:07:43.632962+00:00
-- url     : https://prove2.me/theorems/a1cd5b8f-cda4-418b-9e05-747670d22c13
-- title:
--   Freiman.section14_pairWitnesses_0128_0256
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 128).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_0128_0256 : ∀ a ∈ (section14Catalog.assignments.drop 128).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
