-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_AdaptedFrame_finrank_step
-- name    : GlobalTheory.HTLat.AdaptedFrame.finrank_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:37.844818+00:00
-- url     : https://prove2.me/theorems/391624a0-8663-513c-a692-76c8cbace97d
-- title:
--   Adapted Frame: finrank step
-- statement:
--   The Adapted Frame construction uses the finrank step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L458-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L458-L462

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

theorem GlobalTheory.HTLat.AdaptedFrame.finrank_step {W U₁ : Submodule C U} {j : ℕ} (F : AdaptedFrame W U₁ N j)
    {i : ℕ} (hi : i ≤ N) : Module.finrank C (step C F.f i) = i := by sorry
