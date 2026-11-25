-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_nonempty_adaptedFrame
-- name    : GlobalTheory.HTLat.nonempty_adaptedFrame
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:32.816798+00:00
-- url     : https://prove2.me/theorems/748cdb93-98c1-4eaa-bce6-84bcb5479685
-- title:
--   HTLat: nonempty adapted Frame
-- statement:
--   The HTLat construction uses the nonempty adapted Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L474-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L474-L502

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

theorem GlobalTheory.HTLat.nonempty_adaptedFrame {W U₁ : Submodule C U} (h : W ≤ U₁) [FiniteDimensional C U₁] :
    Nonempty (AdaptedFrame W U₁ (Module.finrank C U₁) (Module.finrank C W)) := by sorry
