-- Prove2me | Theorems.Thm_GlobalTheory_IsBicharacter_mul
-- name    : GlobalTheory.IsBicharacter.mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:08.246203+00:00
-- url     : https://prove2.me/theorems/ea23e873-a3bd-4264-b297-1cbf4e8aac57
-- title:
--   Is Bicharacter: mul
-- statement:
--   The Is Bicharacter construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1249-L1251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1249-L1251

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
open Algebra.TensorProduct (productMap)
variable (R : Type*) {H K : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [CommSemiring K] [Bialgebra R K]
variable {R} {u v : H ⊗[R] K}
open GlobalTheory.IsBicharacter

theorem GlobalTheory.IsBicharacter.mul (hu : IsBicharacter R u) (hv : IsBicharacter R v) : IsBicharacter R (u * v) := by sorry
