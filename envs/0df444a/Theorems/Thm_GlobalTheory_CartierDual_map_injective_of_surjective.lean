-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_map_injective_of_surjective
-- name    : GlobalTheory.CartierDual.map_injective_of_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:58.210051+00:00
-- url     : https://prove2.me/theorems/9f80016e-0dc3-4458-a99c-6842dbf796c4
-- title:
--   Cartier Dual: map injective of surjective
-- statement:
--   The Cartier Dual construction uses the map injective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L450-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L450-L452

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
variable {R H K L : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
  [Semiring L] [Bialgebra R L] [Module.Finite R L] [Module.Projective R L]

theorem GlobalTheory.CartierDual.map_injective_of_surjective {f : H →ₐc[R] K} (hf : Function.Surjective f) :
    Function.Injective (map f) := by sorry
