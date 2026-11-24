-- Prove2me | Theorems.Thm_GlobalTheory_BCT_SuppFin_finite_of_valuation_bounded_of_norm_le_one
-- name    : GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:43.61314+00:00
-- url     : https://prove2.me/theorems/859f71f3-75e4-414f-a6cd-3d08a4465e1c
-- title:
--   Supp Fin: finite of valuation bounded of norm le one
-- statement:
--   The Supp Fin construction uses the finite of valuation bounded of norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOne.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOne.lean#L17-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin

theorem GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one :
    ∀ (E : Type) [Field E] [NumberField E] (X : Set E),
      (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) →
      (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by sorry
