-- Prove2me | Theorems.Thm_GlobalTheory_pullbackPointEquiv_mul
-- name    : GlobalTheory.pullbackPointEquiv_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:43.763131+00:00
-- url     : https://prove2.me/theorems/cd3ddf2d-2110-5781-98d3-d9e601ceed87
-- title:
--   Global Theory: pullback Point Equiv mul
-- statement:
--   The Global Theory construction uses the pullback Point Equiv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L146-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem GlobalTheory.pullbackPointEquiv_mul [GrpObj G] (h : IsPullback φ G'.hom G.hom f) {T : Over S'}
    (x y : T ⟶ G') :
    letI := grpObjOfIsPullback h
    pullbackPointEquiv h T (x * y) = pullbackPointEquiv h T x * pullbackPointEquiv h T y := by sorry
