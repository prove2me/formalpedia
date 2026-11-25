-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_main
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:27.87869+00:00
-- url     : https://prove2.me/theorems/e77feb09-b205-5464-998b-13aa2ac9c048
-- title:
--   Left Shift: main
-- statement:
--   The Left Shift construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L109-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L109-L218

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.main : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℂ → ℂ) (A x a b : ℝ), 0 ≤ A → 2 ≤ x → a ≤ b → 1 ≤ |a| → 1 ≤ |b| → (∀ s : ℂ, s.re ≤ -(1 / 2) → a ≤ s.im → s.im ≤ b → DifferentiableAt ℂ G s ∧ ‖G s‖ ≤ A * (1 + |s.re| + |s.im|)) → ‖∫ t : ℝ in a..b, G (((-(1/2) : ℝ) : ℂ) + t * I) * (x : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ K * A := by sorry
