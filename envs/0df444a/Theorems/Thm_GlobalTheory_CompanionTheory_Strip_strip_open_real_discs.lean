-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Strip_strip_open_real_discs
-- name    : GlobalTheory.CompanionTheory.Strip.strip_open_real_discs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:32:12.737845+00:00
-- url     : https://prove2.me/theorems/295fb09d-f737-47d9-b909-5fe72681c69a
-- title:
--   Strip: strip open real discs
-- statement:
--   The Strip construction uses the strip open real discs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripOpenRealDiscs.lean#L5-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripOpenRealDiscs.lean#L5-L55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripOpenRealDiscs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Strip

theorem GlobalTheory.CompanionTheory.Strip.strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by sorry
