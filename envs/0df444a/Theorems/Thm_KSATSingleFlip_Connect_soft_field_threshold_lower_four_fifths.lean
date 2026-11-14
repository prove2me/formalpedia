-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_lower_four_fifths
-- name    : KSATSingleFlip.Connect.soft_field_threshold_lower_four_fifths
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:06:17.47196+00:00
-- url     : https://prove2.me/theorems/ce5e832a-f1b7-4fe2-9b74-91af1fc80c61
-- title:
--   The k-SAT soft-field critical threshold is at least four fifths
-- statement:
--   If γ ≤ 4/5, the supremum of the masses of the soft-field iterates is infinite. Therefore γ* ≥ 4/5. This is a partial result toward the sharper γ* ≥ c₀ = 2(√2−1) in Theorem 4.4.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and Theorem 4.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_threshold_lower_four_fifths :
    (∀ γ : ℝ, γ ≤ 4/5 → (⨆ r : ℕ, mIter γ r) = ∞) ∧
    (4/5 : ℝ) ≤ gammaStar := by sorry
