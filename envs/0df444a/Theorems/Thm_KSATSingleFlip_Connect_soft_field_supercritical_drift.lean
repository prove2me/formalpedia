-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_supercritical_drift
-- name    : KSATSingleFlip.Connect.soft_field_supercritical_drift
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:16:35.083429+00:00
-- url     : https://prove2.me/theorems/fa0582e1-0bd0-4981-8d32-f5ea1ed6abb0
-- title:
--   Supercritical drift of the soft-field potential
-- statement:
--   There is an absolute ε₀ in (0,1/10) such that, for γ ≤ 1, 0 < ε ≤ ε₀, r ≥ 1, mᵣ ≤ 16 and mᵣ₊₁ ≥ 1+ε, the potential increment satisfies hᵣ₊₁−hᵣ ≥ ε²/7. This is the complete supercritical drift assertion of Lemma 4.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 4.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_supercritical_drift :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < 1/10 ∧ ∀ (γ ε : ℝ) (r : ℕ),
      γ ≤ 1 → 0 < ε → ε ≤ ε0 → 1 ≤ r →
      (massM (nuIter γ r)).toReal ≤ 16 →
      1 + ε ≤ (massM (nuIter γ (r+1))).toReal →
      ε^2/7 ≤ hPot (nuIter γ (r+1)) - hPot (nuIter γ r) := by sorry
