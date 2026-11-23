-- Prove2me | Theorems.Thm_GlobalTheory_exists_coeffSup_eq
-- name    : GlobalTheory.exists_coeffSup_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:48.684196+00:00
-- url     : https://prove2.me/theorems/e5b2e9b2-7eaa-487c-b8b2-15be848856e4
-- title:
--   Global Theory: exists coeff Sup eq
-- statement:
--   The Global Theory construction uses the exists coeff Sup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L44-L49

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

theorem GlobalTheory.exists_coeffSup_eq [Nonempty ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    ∃ i, coeffSup N c = N (c i) := by sorry
