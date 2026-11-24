-- Prove2me | Theorems.Thm_GlobalTheory_coeffSup_eq_sup_univ
-- name    : GlobalTheory.coeffSup_eq_sup_univ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:14.39283+00:00
-- url     : https://prove2.me/theorems/b8261ff2-1af2-416a-8bd2-44cd4875263d
-- title:
--   Global Theory: coeff Sup eq sup univ
-- statement:
--   The Global Theory construction uses the coeff Sup eq sup univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L64-L66

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

theorem GlobalTheory.coeffSup_eq_sup_univ [Fintype ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    coeffSup N c = Finset.univ.sup fun i => N (c i) := by sorry
