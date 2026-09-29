-- Prove2me | Theorems.Thm_MTT_Eigenform_coeff_mem_ringOfIntegers
-- name    : MTT.Eigenform.coeff_mem_ringOfIntegers
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T07:00:40.34499+00:00
-- url     : https://prove2.me/theorems/7381859f-2a7f-408b-a023-52687a33a08e
-- title:
--   Fourier coefficients lie in the ring of integers of the coefficient field
-- statement:
--   Let $f$ be an MTT eigenform of positive level and weight at least two, and let $K_f$ be its coefficient field. Every Fourier coefficient $a_n(f)$, viewed as an element of $K_f$, lies in the integral closure of $\mathbf Z$ in $K_f$:
--
--   $$
--   a_n(f)\in\mathcal O_{K_f}.
--   $$
--
--   This upgrades the previously established algebraic integrality of $a_n(f)$ in $\overline{\mathbf Q}$ to literal membership in the integer ring of the canonical coefficient field.
-- source:
--   Standard algebraicity and integrality properties of normalized cuspidal Hecke eigenforms; coefficient-field notation as in Kriz--Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4, p. 27, https://arxiv.org/pdf/2310.20678

import Definitions.Def_MTT_EigenformCoefficientField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

/-- Every Fourier coefficient, regarded as an element of the coefficient
field, belongs to its ring of integers. -/
theorem MTT.Eigenform.coeff_mem_ringOfIntegers
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    (⟨f.coeff n, f.coeff_mem_coefficientField n⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by sorry
