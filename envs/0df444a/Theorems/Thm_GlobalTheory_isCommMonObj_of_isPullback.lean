-- Prove2me | Theorems.Thm_GlobalTheory_isCommMonObj_of_isPullback
-- name    : GlobalTheory.isCommMonObj_of_isPullback
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:59.850114+00:00
-- url     : https://prove2.me/theorems/e56263a2-747c-50f1-8a7b-4fd36cd88c02
-- title:
--   Global Theory: is Comm Mon Obj of is Pullback
-- statement:
--   The Global Theory construction uses the is Comm Mon Obj of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L153-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L153-L165

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

theorem GlobalTheory.isCommMonObj_of_isPullback [GrpObj G] [IsCommMonObj G]
    (h : IsPullback φ G'.hom G.hom f) :
    letI := grpObjOfIsPullback h
    IsCommMonObj G' := by sorry
