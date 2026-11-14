-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_intensity_identity
-- name    : KSATSingleFlip.Connect.soft_field_potential_intensity_identity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:46:04.610636+00:00
-- url     : https://prove2.me/theorems/09c327f0-50c7-4a64-84aa-96cf6593d9f7
-- title:
--   Soft-field potential integrand as the symmetrized intensity
-- statement:
--   For every real z, cosh(z)g(q(z)) equals w(z)+w(−z)−2 cosh(z). This pointwise identity connects the potential to the positive and negative jump intensities in the Poisson tilting formula.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open KSATSingleFlip.Connect
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_potential_intensity_identity (z : ℝ) :
    Real.cosh z * gW (qOf z) = wInt z+wInt (-z)-2*Real.cosh z := by sorry
