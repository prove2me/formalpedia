-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_bounds
-- name    : KSATSingleFlip.Connect.soft_field_potential_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:12:26.499821+00:00
-- url     : https://prove2.me/theorems/5bfa0117-d572-4595-b272-7cda9fe86883
-- title:
--   Soft-field potential is integrable and bounded by mass
-- statement:
--   For every finite soft-field measure, the integrand cosh(z)g(q(z)) is integrable and the potential h lies between zero and the total mass. This uses the pointwise inequalities 0 ≤ g ≤ f and the normalization cosh(z)f(q(z))=1 in Section 4.1.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, equation (4.1) and Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_potential_bounds (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z => Real.cosh z * gW (qOf z)) ν ∧
    0 ≤ hPot ν ∧ hPot ν ≤ (massM ν).toReal := by sorry
