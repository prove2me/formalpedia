-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
-- name    : KSATSingleFlip.Connect.soft_field_mass_identity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:22.653204+00:00
-- url     : https://prove2.me/theorems/878dbd40-8bf0-47f5-92c3-aa527337e71d
-- title:
--   Soft-field mass normalization
-- statement:
--   For every real half-log-odds z, q(z) lies strictly between 0 and 1 and cosh(z) f(q(z)) equals 1. This identity turns the f-weighted pairing into the total mass of the soft-field measure.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, equation (4.1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem KSATSingleFlip.Connect.soft_field_mass_identity (z : ℝ) :
    0 < qOf z ∧ qOf z < 1 ∧ Real.cosh z * fW (qOf z) = 1 := by sorry
