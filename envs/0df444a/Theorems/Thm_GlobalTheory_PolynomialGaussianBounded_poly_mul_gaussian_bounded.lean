-- Prove2me | Theorems.Thm_GlobalTheory_PolynomialGaussianBounded_poly_mul_gaussian_bounded
-- name    : GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:30.39119+00:00
-- url     : https://prove2.me/theorems/a28e2a62-d031-4b8f-a640-f88470ce574b
-- title:
--   Polynomial Gaussian Bounded: poly mul gaussian bounded
-- statement:
--   The Polynomial Gaussian Bounded construction uses the poly mul gaussian bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolyMulGaussianBounded.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolyMulGaussianBounded.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialGaussianBounded

theorem GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded :
    ∀ (c : ℝ), (0 : ℝ) < c → ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r →
      ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by sorry
