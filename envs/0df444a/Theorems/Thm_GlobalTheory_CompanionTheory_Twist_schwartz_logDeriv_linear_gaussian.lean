-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Twist_schwartz_logDeriv_linear_gaussian
-- name    : GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:27:05.274114+00:00
-- url     : https://prove2.me/theorems/7693bd38-10e5-4f22-9122-27a23d06a4c1
-- title:
--   Twist: schwartz log Deriv linear gaussian
-- statement:
--   The Twist construction uses the schwartz log Deriv linear gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SchwartzLogDerivLinearGaussian.lean#L41-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SchwartzLogDerivLinearGaussian.lean#L41-L90

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SchwartzLogDerivLinearGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist

theorem GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by sorry
