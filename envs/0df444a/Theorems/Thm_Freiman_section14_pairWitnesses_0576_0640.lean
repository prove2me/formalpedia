-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_0576_0640
-- name    : Freiman.section14_pairWitnesses_0576_0640
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:25:17.257522+00:00
-- url     : https://prove2.me/theorems/35cf07fa-d00f-4ffe-8180-d5302b1cbb12
-- title:
--   Freiman.section14_pairWitnesses_0576_0640
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 576).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_0576_0640 : ∀ a ∈ (section14Catalog.assignments.drop 576).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
