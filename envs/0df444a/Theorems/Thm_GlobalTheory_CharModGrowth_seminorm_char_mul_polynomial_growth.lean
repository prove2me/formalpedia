-- Prove2me | Theorems.Thm_GlobalTheory_CharModGrowth_seminorm_char_mul_polynomial_growth
-- name    : GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:38.451794+00:00
-- url     : https://prove2.me/theorems/237babb2-d7fa-4e5f-a344-857b8a1e3579
-- title:
--   Char Mod Growth: seminorm char mul polynomial growth
-- statement:
--   The Char Mod Growth construction uses the seminorm char mul polynomial growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModulatedSchwartzSeminormPolynomial.lean#L66-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModulatedSchwartzSeminormPolynomial.lean#L66-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModulatedSchwartzSeminormPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharModGrowth

theorem GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by sorry
