-- Prove2me | Theorems.Thm_GlobalTheory_residueFieldMap_surjective_of_mono
-- name    : GlobalTheory.residueFieldMap_surjective_of_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:57.222215+00:00
-- url     : https://prove2.me/theorems/0377170b-a0bf-4fff-8174-2b8698cdb6c2
-- title:
--   Global Theory: residue Field Map surjective of mono
-- statement:
--   The Global Theory construction uses the residue Field Map surjective of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMono.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMono.lean#L26-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory

theorem GlobalTheory.residueFieldMap_surjective_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by sorry
