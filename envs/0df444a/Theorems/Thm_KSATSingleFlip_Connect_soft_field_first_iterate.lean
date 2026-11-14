-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_first_iterate
-- name    : KSATSingleFlip.Connect.soft_field_first_iterate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:10:46.223713+00:00
-- url     : https://prove2.me/theorems/545c6852-4a79-47ca-9a7d-8660fa868ae1
-- title:
--   First soft-field iterate and its exact mass and potential
-- statement:
--   The first soft-field iterate is the point mass at zero with weight exp(−γ). Its mass is exp(−γ) and its potential is c₀ exp(−γ), where c₀ = 2(√2−1). This is the initial-value identity used in equation (4.12).
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_first_iterate (γ : ℝ) :
    nuIter γ 1 = ENNReal.ofReal (Real.exp (-γ)) • Measure.dirac (0:ℝ) ∧
    (massM (nuIter γ 1)).toReal = Real.exp (-γ) ∧
    hPot (nuIter γ 1) = c0 * Real.exp (-γ) := by sorry
