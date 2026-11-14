-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_lower_if_bounded_masses_at_most_one
-- name    : KSATSingleFlip.Connect.soft_field_threshold_lower_if_bounded_masses_at_most_one
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:17:59.986297+00:00
-- url     : https://prove2.me/theorems/e0114601-5cf1-4121-9262-0b81645c31f9
-- title:
--   Critical threshold lower bound from bounded-mass control
-- statement:
--   Assume that for each γ every bounded soft-field mass sequence stays at most one. Then the threshold obeys γ* ≥ c₀. The mass bound assumption is the outstanding supercritical control; it is not asserted unconditionally here.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Theorem 4.4 and Lemmas 4.5–4.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_threshold_lower_if_bounded_masses_at_most_one
    (hbounded : ∀ γ : ℝ, (⨆ r : ℕ, mIter γ r) < ∞ → ∀ r : ℕ, mIter γ r ≤ 1) :
    c0 ≤ gammaStar := by sorry
