-- Prove2me | Theorems.Thm_GlobalTheory_CartierDual_map_injective
-- name    : GlobalTheory.CartierDual.map_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:49.775857+00:00
-- url     : https://prove2.me/theorems/29f51967-cfc9-45d2-94a9-29c4d9c3adc8
-- title:
--   Cartier Dual: map injective
-- statement:
--   The Cartier Dual construction uses the map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L447-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L447-L448

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

theorem GlobalTheory.CartierDual.map_injective : Function.Injective (map : (H →ₐc[R] K) → _) := by sorry
