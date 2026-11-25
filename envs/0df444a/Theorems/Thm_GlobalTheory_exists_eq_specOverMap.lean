-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_specOverMap
-- name    : GlobalTheory.exists_eq_specOverMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:53.41367+00:00
-- url     : https://prove2.me/theorems/8bb1aee4-f64d-4d80-ba60-f0e337a503bb
-- title:
--   Global Theory: exists eq spec Over Map
-- statement:
--   The Global Theory construction uses the exists eq spec Over Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L26-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem GlobalTheory.exists_eq_specOverMap (x : specOver R B ⟶ specOver R A) :
    ∃ g : A →ₐ[R] B, x = specOverMap g := by sorry
