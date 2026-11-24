-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_isPrimitiveElem_iff_mul
-- name    : GlobalTheory.CartierDual.isPrimitiveElem_iff_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:23.887479+00:00
-- url     : https://prove2.me/theorems/0a63ad6a-1a40-4dae-9a8e-2baa6b50e937
-- title:
--   Cartier Dual: is Primitive Elem iff mul
-- statement:
--   The Cartier Dual construction uses the is Primitive Elem iff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1003-L1007
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1003-L1007

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
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]

theorem GlobalTheory.CartierDual.isPrimitiveElem_iff_mul (a : H) : IsPrimitiveElem R a ↔
    ∀ φ ψ : CartierDual R H, (φ * ψ) a = φ 1 * ψ a + ψ 1 * φ a := by sorry
