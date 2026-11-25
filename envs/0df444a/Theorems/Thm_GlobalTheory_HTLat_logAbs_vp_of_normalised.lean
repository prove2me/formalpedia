-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_logAbs_vp_of_normalised
-- name    : GlobalTheory.HTLat.logAbs_vp_of_normalised
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:24.667415+00:00
-- url     : https://prove2.me/theorems/9709885f-4d7a-45b4-b811-a41a86bbe9a2
-- title:
--   HTLat: log Abs vp of normalised
-- statement:
--   The HTLat construction uses the log Abs vp of normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L519-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L519-L523

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

theorem GlobalTheory.HTLat.logAbs_vp_of_normalised {p : ℕ} (hp : 1 < p) (v : Valuation C ℝ≥0)
    (h : v (p : C) = (p : ℝ≥0)⁻¹) (r : ℝ≥0) : logAbs_vp p v r = Real.log r := by sorry
