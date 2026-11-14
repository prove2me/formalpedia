-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_tilt_identities
-- name    : KSATSingleFlip.Connect.soft_field_tilt_identities
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:45:21.386181+00:00
-- url     : https://prove2.me/theorems/07850141-a990-495f-b71c-db0d723af109
-- title:
--   Exact exponential tilts of the soft-field intensity
-- statement:
--   For every real z, w(z)e^{a(z)}=2 cosh(z) and w(z)e^{−a(z)}=e^z for the intensity and jump in Definition 4.2. These exact identities control the exponential moments and Poisson tilting of the soft-field kernel.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem KSATSingleFlip.Connect.soft_field_tilt_identities (z : ℝ) :
    wInt z * Real.exp (aShift z) = 2*Real.cosh z ∧
    wInt z * Real.exp (-aShift z) = Real.exp z := by sorry
