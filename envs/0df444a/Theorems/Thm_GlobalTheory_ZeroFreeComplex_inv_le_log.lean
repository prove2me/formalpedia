-- Prove2me | Theorems.Thm_GlobalTheory_ZeroFreeComplex_inv_le_log
-- name    : GlobalTheory.ZeroFreeComplex.inv_le_log
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:04:17.021823+00:00
-- url     : https://prove2.me/theorems/483101d0-cea3-4f03-8339-c0ba2ac5a61f
-- title:
--   Zero Free Complex: inv le log
-- statement:
--   The Zero Free Complex construction uses the inv le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionConjEqZero.lean#L173-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionConjEqZero.lean#L173-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex

theorem GlobalTheory.ZeroFreeComplex.inv_le_log : ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ γ : ℝ), χ ≠ 1 → LFunction χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ ^ 2 ≠ 1 ∨ γ ≠ 0) →
    0 < δ → δ ≤ 1 / 21 → 1 / δ ≤ K * Real.log (q * (|γ| + 2)) := by sorry
