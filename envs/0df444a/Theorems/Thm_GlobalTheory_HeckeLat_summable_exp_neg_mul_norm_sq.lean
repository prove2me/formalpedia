-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLat_summable_exp_neg_mul_norm_sq
-- name    : GlobalTheory.HeckeLat.summable_exp_neg_mul_norm_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:21.101483+00:00
-- url     : https://prove2.me/theorems/ff9a02d6-fac9-4093-a1be-dbab119a82c2
-- title:
--   Hecke Lat: summable exp neg mul norm sq
-- statement:
--   The Hecke Lat construction uses the summable exp neg mul norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L53-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
omit [Fintype I]

theorem GlobalTheory.HeckeLat.summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by sorry
