-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_finite_generation
-- name    : MTT.Cohomology.integral_finite_generation
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T13:59:39.580351+00:00
-- url     : https://prove2.me/theorems/30b13f80-97ec-4333-8b8b-c59fb1ae29ea
-- title:
--   Finite generation of integral compactly supported cohomology
-- statement:
--   The integral compactly supported group cohomology of Γ₁(N), with homogeneous degree-n binary polynomial coefficients, is a finitely generated Z-module. A proof may use finitely many Manin generators; no torsion-free assumption on Γ₁(N) is imposed.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, Definition 4.1 and Proposition 4.2, pp. 861–863, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf. Integral statements use relative group cohomology, not the coarse quotient at elliptic points. Finite generation follows from finite-index Manin generators and finite-rank coefficient modules.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_finite_generation
    {N n : ℕ} (hN : 0 < N) : Module.Finite ℤ (Hc N n ℤ) := by sorry
