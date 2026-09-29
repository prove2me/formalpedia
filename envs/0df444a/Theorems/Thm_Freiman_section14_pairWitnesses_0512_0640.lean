-- Prove2me | Theorems.Thm_Freiman_section14_pairWitnesses_0512_0640
-- name    : Freiman.section14_pairWitnesses_0512_0640
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T10:04:05.808691+00:00
-- url     : https://prove2.me/theorems/38ea4425-3338-4875-8322-10ee00389fd0
-- title:
--   Freiman.section14_pairWitnesses_0512_0640
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ a ∈ (section14Catalog.assignments.drop 512).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_pairWitnesses_0512_0640 : ∀ a ∈ (section14Catalog.assignments.drop 512).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by sorry
