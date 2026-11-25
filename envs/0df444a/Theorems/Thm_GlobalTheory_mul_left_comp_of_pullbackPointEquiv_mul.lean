-- Prove2me | Theorems.Thm_GlobalTheory_mul_left_comp_of_pullbackPointEquiv_mul
-- name    : GlobalTheory.mul_left_comp_of_pullbackPointEquiv_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:26.670797+00:00
-- url     : https://prove2.me/theorems/8113cee7-31bf-447f-a4d9-a03395608999
-- title:
--   Global Theory: mul left comp of pullback Point Equiv mul
-- statement:
--   The Global Theory construction uses the mul left comp of pullback Point Equiv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L167-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L167-L183

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

theorem GlobalTheory.mul_left_comp_of_pullbackPointEquiv_mul [GrpObj G] [GrpObj G']
    (h : IsPullback φ G'.hom G.hom f) {T' : Over S'} {T : Over S} (t : T'.left ⟶ T.left)
    {x' y' : T' ⟶ G'} {x y : T ⟶ G}
    (hm : pullbackPointEquiv h T' (x' * y') =
      pullbackPointEquiv h T' x' * pullbackPointEquiv h T' y')
    (hx : x'.left ≫ φ = t ≫ x.left) (hy : y'.left ≫ φ = t ≫ y.left) :
    (x' * y').left ≫ φ = t ≫ (x * y).left := by sorry
