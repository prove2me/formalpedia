-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_pointsEquiv_comp
-- name    : GlobalTheory.CartierDual.pointsEquiv_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:14.929804+00:00
-- url     : https://prove2.me/theorems/72df2d5b-f787-5c1a-acd8-573ab49bb705
-- title:
--   Cartier Dual: points Equiv comp
-- statement:
--   The Cartier Dual construction uses the points Equiv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L814-L819
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L814-L819

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open GlobalTheory.CartierDual
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
variable {A : Type*} [CommSemiring A] [Algebra R A]

theorem GlobalTheory.CartierDual.pointsEquiv_comp {B : Type*} [CommSemiring B] [Algebra R B] (g : A →ₐ[R] B)
    (f : CartierDual R C →ₐ[R] A) :
    (pointsEquiv R C B (g.comp f)).val =
      LinearMap.rTensor C g.toLinearMap (pointsEquiv R C A f).val := by sorry
