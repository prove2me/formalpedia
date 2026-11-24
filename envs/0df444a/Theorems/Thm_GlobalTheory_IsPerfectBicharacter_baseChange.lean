-- Prove2me | Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
-- name    : GlobalTheory.IsPerfectBicharacter.baseChange
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:34.868789+00:00
-- url     : https://prove2.me/theorems/f49cea79-5ee8-4e52-9c2d-fb82a6de278b
-- title:
--   Is Perfect Bicharacter: base Change
-- statement:
--   The Is Perfect Bicharacter construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1489-L1497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1489-L1497

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
variable (A : Type*) [CommSemiring A] [Algebra R A]
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]

theorem GlobalTheory.IsPerfectBicharacter.baseChange (hu : IsPerfectBicharacter R u) :
    IsPerfectBicharacter A (pairingBaseChange A u) := by sorry
