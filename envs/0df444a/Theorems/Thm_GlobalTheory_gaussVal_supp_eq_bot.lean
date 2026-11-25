-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_supp_eq_bot
-- name    : GlobalTheory.gaussVal_supp_eq_bot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:02.618804+00:00
-- url     : https://prove2.me/theorems/769cb39d-9942-44b7-b562-c6628ed10dc9
-- title:
--   Global Theory: gauss Val supp eq bot
-- statement:
--   The Global Theory construction uses the gauss Val supp eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L344-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L344-L345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)

theorem GlobalTheory.gaussVal_supp_eq_bot : (gaussVal (σ := σ) v).supp = ⊥ := by sorry
