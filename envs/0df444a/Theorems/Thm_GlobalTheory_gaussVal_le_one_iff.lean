-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_le_one_iff
-- name    : GlobalTheory.gaussVal_le_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:08.756921+00:00
-- url     : https://prove2.me/theorems/addc7533-0391-4508-9649-9d45285fcdb9
-- title:
--   Global Theory: gauss Val le one iff
-- statement:
--   The Global Theory construction uses the gauss Val le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L363-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L363-L373

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
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem GlobalTheory.gaussVal_le_one_iff {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    {f : MvPolynomial σ K} :
    gaussVal v f ≤ 1 ↔ ∃ g : MvPolynomial σ O, map (algebraMap O K) g = f := by sorry
