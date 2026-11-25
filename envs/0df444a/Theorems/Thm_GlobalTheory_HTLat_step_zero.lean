-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_step_zero
-- name    : GlobalTheory.HTLat.step_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:21.034219+00:00
-- url     : https://prove2.me/theorems/01f3972b-ca8b-4350-9155-c52791188e54
-- title:
--   HTLat: step zero
-- statement:
--   The HTLat construction uses the step zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L290-L292

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}

theorem GlobalTheory.HTLat.step_zero (f : Fin N → U) :
    _root_.GlobalTheory.HTLat.step C f 0 = ⊥ := by sorry
