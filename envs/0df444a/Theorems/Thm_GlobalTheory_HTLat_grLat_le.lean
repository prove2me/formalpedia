-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_grLat_le
-- name    : GlobalTheory.HTLat.grLat_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:30.199229+00:00
-- url     : https://prove2.me/theorems/1421203a-267d-4c34-b618-7c84958e0f99
-- title:
--   HTLat: gr Lat le
-- statement:
--   The HTLat construction uses the gr Lat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L142-L145

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

theorem GlobalTheory.HTLat.grLat_le (La : Submodule O U) (F' F : Submodule C U) :
    grLat La F' F ≤ (F.map F'.mkQ).restrictScalars O := by sorry
