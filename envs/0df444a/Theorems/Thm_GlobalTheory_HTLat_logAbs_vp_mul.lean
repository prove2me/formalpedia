-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_logAbs_vp_mul
-- name    : GlobalTheory.HTLat.logAbs_vp_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:16.336725+00:00
-- url     : https://prove2.me/theorems/66bea836-6080-5e13-86e4-219e188a4b36
-- title:
--   HTLat: log Abs vp mul
-- statement:
--   The HTLat construction uses the log Abs vp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L507-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L507-L511

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

theorem GlobalTheory.HTLat.logAbs_vp_mul (p : ℕ) (v : Valuation C ℝ≥0) {r s : ℝ≥0} (hr : r ≠ 0) (hs : s ≠ 0) :
    logAbs_vp p v (r * s) = logAbs_vp p v r + logAbs_vp p v s := by sorry
