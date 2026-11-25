-- Prove2me | Theorems.Thm_GlobalTheory_Cube_degProj_mul_degProj
-- name    : GlobalTheory.Cube.degProj_mul_degProj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:44:35.073503+00:00
-- url     : https://prove2.me/theorems/98b36c41-13d1-550f-9a5b-e64a56ff5e86
-- title:
--   Cube: deg Proj mul deg Proj
-- statement:
--   The Cube construction uses the deg Proj mul deg Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L81-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]

theorem GlobalTheory.Cube.degProj_mul_degProj (A : Cube.{v} ι R) (p q : ℕ) :
    degProj A p * degProj A q = if p = q then degProj A p else 0 := by sorry
