-- Prove2me | Theorems.Thm_GlobalTheory_coeffSup_lt_iff
-- name    : GlobalTheory.coeffSup_lt_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:53.168873+00:00
-- url     : https://prove2.me/theorems/7b68c10e-3340-4845-b5c0-dffd7fd865e9
-- title:
--   Global Theory: coeff Sup lt iff
-- statement:
--   The Global Theory construction uses the coeff Sup lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L28-L35

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
variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]
variable {N : M → Γ₀}

theorem GlobalTheory.coeffSup_lt_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} (hγ : γ ≠ 0) :
    coeffSup N c < γ ↔ ∀ i, N (c i) < γ := by sorry
