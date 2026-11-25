-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_fg_grLat
-- name    : GlobalTheory.HTLat.fg_grLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:18.370957+00:00
-- url     : https://prove2.me/theorems/2b7f8214-c31a-56ed-8295-4da33f1d4f2e
-- title:
--   HTLat: fg gr Lat
-- statement:
--   The HTLat construction uses the fg gr Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L272-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L272-L273

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
variable (v : Valuation C ℝ≥0)
variable {v}

theorem GlobalTheory.HTLat.fg_grLat (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) (F' F : Submodule C U) :
    (grLat La F' F).FG := by sorry
