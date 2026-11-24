-- Prove2me | Theorems.Thm_GlobalTheory_T_polynomial_times_gaussian_bounded
-- name    : GlobalTheory.T.polynomial_times_gaussian_bounded
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:32.488242+00:00
-- url     : https://prove2.me/theorems/6b419288-fb9b-4e28-b7ba-c760e6dbd507
-- title:
--   T: polynomial times gaussian bounded
-- statement:
--   The T construction uses the polynomial times gaussian bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBoundedStatement.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBoundedStatement.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBounded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.polynomial_times_gaussian_bounded : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by sorry
