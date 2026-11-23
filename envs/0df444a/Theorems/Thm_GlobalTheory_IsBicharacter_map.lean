-- Prove2me | Theorems.Thm_GlobalTheory_IsBicharacter_map
-- name    : GlobalTheory.IsBicharacter.map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:37.983103+00:00
-- url     : https://prove2.me/theorems/46488206-4b00-4fce-833e-3f9975b64a43
-- title:
--   Is Bicharacter: map
-- statement:
--   The Is Bicharacter construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1442-L1455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1442-L1455

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
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}

theorem GlobalTheory.IsBicharacter.map {H' K' : Type*} [CommSemiring H'] [Bialgebra R H'] [CommSemiring K']
    [Bialgebra R K'] (hu : IsBicharacter R u) (f : H →ₐc[R] H') (g : K →ₐc[R] K') :
    IsBicharacter R (Algebra.TensorProduct.map (f : H →ₐ[R] H') (g : K →ₐ[R] K') u) := by sorry
