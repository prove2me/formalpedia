-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_AdaptedFrame_notMem_step
-- name    : GlobalTheory.HTLat.AdaptedFrame.notMem_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:01.043952+00:00
-- url     : https://prove2.me/theorems/f11a6bb1-fbcc-463f-b5ca-b451cc8ed8cf
-- title:
--   Adapted Frame: not Mem step
-- statement:
--   The Adapted Frame construction uses the not Mem step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L454-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L454-L456

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

theorem GlobalTheory.HTLat.AdaptedFrame.notMem_step {W U₁ : Submodule C U} {j : ℕ} (F : AdaptedFrame W U₁ N j)
    (i : Fin N) : F.f i ∉ step C F.f i := by sorry
