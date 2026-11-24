-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Twist_FockLogDeriv_main
-- name    : GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:26:47.467635+00:00
-- url     : https://prove2.me/theorems/c8be82bd-8140-41ef-adf8-8e71d195ad03
-- title:
--   Fock Log Deriv: main
-- statement:
--   The Fock Log Deriv construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/EqZeroOfForallNhds.lean#L27-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/EqZeroOfForallNhds.lean#L27-L123

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_EqZeroOfForallNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist GlobalTheory.CompanionTheory.Twist.FockLogDeriv

theorem GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (Jm : V × V →ₗ[ℝ] V × V) (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (hE : ∀ (p : V × V) (y : V), fderiv ℝ f₀ y (Jm p).1
        + (-(2 * Real.pi * Complex.I)) * ((T y (Jm p).2 : ℝ) : ℂ) * f₀ y
      = Complex.I * (fderiv ℝ f₀ y p.1
        + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y)) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ, ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y := by sorry
