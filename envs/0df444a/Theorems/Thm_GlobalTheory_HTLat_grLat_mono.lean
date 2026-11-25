-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_grLat_mono
-- name    : GlobalTheory.HTLat.grLat_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:42.065798+00:00
-- url     : https://prove2.me/theorems/a91433b1-56d0-4515-ac79-907b9f1d5f60
-- title:
--   HTLat: gr Lat mono
-- statement:
--   The HTLat construction uses the gr Lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L139-L140

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

theorem GlobalTheory.HTLat.grLat_mono {La La' : Submodule O U} (h : La ≤ La') (F' F : Submodule C U) :
    grLat La F' F ≤ grLat La' F' F := by sorry
