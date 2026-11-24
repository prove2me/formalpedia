-- Prove2me | Theorems.Thm_GlobalTheory_additive_poly_taylor_coeff_sub_norm_le
-- name    : GlobalTheory.additive_poly_taylor_coeff_sub_norm_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:03.416537+00:00
-- url     : https://prove2.me/theorems/60904eaf-7876-4a74-b98d-c1a6d547c942
-- title:
--   Global Theory: additive poly taylor coeff sub norm le
-- statement:
--   The Global Theory construction uses the additive poly taylor coeff sub norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditivePolyTaylorCoeffSubNormLe.lean#L6-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditivePolyTaylorCoeffSubNormLe.lean#L6-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.additive_poly_taylor_coeff_sub_norm_le :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by sorry
