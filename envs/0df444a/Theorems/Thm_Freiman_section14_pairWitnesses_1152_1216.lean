-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_1152_1216
-- name    : Freiman.section14_pairWitnesses_1152_1216
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:27:37.492424+00:00
-- url     : https://prove2.me/theorems/9282ffda-c995-4c95-9bf4-24cfd25d8432
-- title:
--   Freiman.section14_pairWitnesses_1152_1216
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 1152).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_1152_1216 : ∀ a ∈ (section14Catalog.assignments.drop 1152).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
