-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_intensity_bound
-- name    : KSATSingleFlip.Connect.soft_field_intensity_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:25:02.429246+00:00
-- url     : https://prove2.me/theorems/a9fde7a7-5736-494f-9cd3-1db7784756cc
-- title:
--   Soft-field Poisson intensity is bounded by twice cosh
-- statement:
--   For every real z, the soft-field Poisson intensity w(z)=√(1+e^{2z}) is at most 2 cosh(z). Consequently finite scaled unfrozen mass controls the intensity needed to define the compound Poisson update.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem KSATSingleFlip.Connect.soft_field_intensity_bound (z : ℝ) : wInt z ≤ 2*Real.cosh z := by sorry
