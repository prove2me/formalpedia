-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_span_eq_top_of_rat
-- name    : GlobalTheory.TensorLat.span_eq_top_of_rat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:07:36.305262+00:00
-- url     : https://prove2.me/theorems/fe836a41-e7ea-474b-8551-892306e8ede8
-- title:
--   Tensor Lat: span eq top of rat
-- statement:
--   The Tensor Lat construction uses the span eq top of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LeMulNormFlatOfSelfDual.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LeMulNormFlatOfSelfDual.lean#L54-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
omit [IsCMField E]

theorem GlobalTheory.TensorLat.span_eq_top_of_rat {S : Set (Fin n → E)} (h : Submodule.span ℚ S = ⊤) :
    Submodule.span E S = ⊤ := by sorry
