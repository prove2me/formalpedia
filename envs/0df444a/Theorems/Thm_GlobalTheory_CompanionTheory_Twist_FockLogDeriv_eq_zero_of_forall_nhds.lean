-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Twist_FockLogDeriv_eq_zero_of_forall_nhds
-- name    : GlobalTheory.CompanionTheory.Twist.FockLogDeriv.eq_zero_of_forall_nhds
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:33.945066+00:00
-- url     : https://prove2.me/theorems/7f2d2da5-03b2-4ca9-ab07-f3699adc9710
-- title:
--   Fock Log Deriv: eq zero of forall nhds
-- statement:
--   The Fock Log Deriv construction uses the eq zero of forall nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/EqZeroOfForallNhds.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/EqZeroOfForallNhds.lean#L7-L25

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

theorem GlobalTheory.CompanionTheory.Twist.FockLogDeriv.eq_zero_of_forall_nhds {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (y₀ : V) (U : Set V) (hU : U ∈ 𝓝 y₀) (b : V) (hb : ∀ y ∈ U, T y b = 0) : b = 0 := by sorry
