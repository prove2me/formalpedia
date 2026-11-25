-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_tensorToHom_apply
-- name    : GlobalTheory.CartierDual.tensorToHom_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:17.503322+00:00
-- url     : https://prove2.me/theorems/a6fcca6a-6a61-5bcd-91f1-8597ce2c2b68
-- title:
--   Cartier Dual: tensor To Hom apply
-- statement:
--   The Cartier Dual construction uses the tensor To Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L680-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L680-L685

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
variable {R N M N' M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

theorem GlobalTheory.CartierDual.tensorToHom_apply (x : N ⊗[R] M) (φ : CartierDual R M) :
    tensorToHom R N M x φ = TensorProduct.rid R N (LinearMap.lTensor N φ.ofConv x) := by sorry
