-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_grLat_eq_inf
-- name    : GlobalTheory.HTLat.grLat_eq_inf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:22.792246+00:00
-- url     : https://prove2.me/theorems/e34d0af5-aac1-4b35-9854-254251944dcc
-- title:
--   HTLat: gr Lat eq inf
-- statement:
--   The HTLat construction uses the gr Lat eq inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L147-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L147-L154

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
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

theorem GlobalTheory.HTLat.grLat_eq_inf (La : Submodule O U) {F' F : Submodule C U} (h : F' ≤ F) :
    grLat La F' F = La.map (F'.mkQ.restrictScalars O) ⊓ (F.map F'.mkQ).restrictScalars O := by sorry
