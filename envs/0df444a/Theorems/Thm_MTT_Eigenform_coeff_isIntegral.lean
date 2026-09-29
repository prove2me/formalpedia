-- Prove2me | Theorems.Thm_MTT_Eigenform_coeff_isIntegral
-- name    : MTT.Eigenform.coeff_isIntegral
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-18T21:19:52.145746+00:00
-- url     : https://prove2.me/theorems/60481847-0538-4fde-9025-e6eb1fcc34d8
-- title:
--   All Fourier coefficients of an MTT eigenform are algebraic integers
-- statement:
--   Every Fourier coefficient a_n(f) of a normalized algebraic Hecke eigenform of positive level and weight at least two is integral over Z.
--
--   The reduction starts from integrality of the prime Hecke eigenvalues. The prime Hecke recurrence expresses a_{ell m} using a_ell, a_m, the nebentypus value at ell, and a_{m/ell}; nebentypus values are zero or roots of unity. Strong induction on n therefore proves the assertion for every coefficient.
-- source:
--   The standard prime Hecke recurrence for normalized eigenforms, using the proved MTT.hasSum_heckePrime node.

import Definitions.Def_MTT_Arithmetic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

theorem MTT.Eigenform.coeff_isIntegral
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    IsIntegral ℤ (f.coeff n) := by
  sorry
