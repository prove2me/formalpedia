-- Prove2me | Theorems.Thm_GlobalTheory_basisMulGL_repr
-- name    : GlobalTheory.basisMulGL_repr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:28.998132+00:00
-- url     : https://prove2.me/theorems/213a46aa-3dc1-5626-9d3b-2ef784b98d67
-- title:
--   Global Theory: basis Mul GL repr
-- statement:
--   The Global Theory construction uses the basis Mul GL repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L82-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.basisMulGL_repr (b : Basis ι R M) (g : GL ι R) (x : M) (i : ι) :
    (basisMulGL b g).repr x i = ∑ j, ((g⁻¹ : GL ι R) : Matrix ι ι R) i j * b.repr x j := by sorry
