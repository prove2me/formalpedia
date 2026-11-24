-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_baseChange_map
-- name    : GlobalTheory.CartierDual.baseChange_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:36.660925+00:00
-- url     : https://prove2.me/theorems/4aee6548-6130-474b-83fe-30bf26cadb43
-- title:
--   Cartier Dual: base Change map
-- statement:
--   The Cartier Dual construction uses the base Change map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L604-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L604-L613

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
variable {R : Type*} (A : Type*) {M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (R) (H : Type*) [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H]
variable {R H}

theorem GlobalTheory.CartierDual.baseChange_map {K : Type*} [Semiring K] [Bialgebra R K] [Module.Finite R K]
    [Module.Projective R K] (f : H →ₐc[R] K) (x : A ⊗[R] CartierDual R K) :
    baseChange R A H (Bialgebra.TensorProduct.map (BialgHom.id A A) (map f) x) =
      map (Bialgebra.TensorProduct.map (BialgHom.id A A) f) (baseChange R A K x) := by sorry
