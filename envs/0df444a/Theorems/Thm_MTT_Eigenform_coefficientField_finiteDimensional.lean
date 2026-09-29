-- Prove2me | Theorems.Thm_MTT_Eigenform_coefficientField_finiteDimensional
-- name    : MTT.Eigenform.coefficientField_finiteDimensional
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T06:48:37.986338+00:00
-- url     : https://prove2.me/theorems/7db18a1c-2fb1-450e-9951-92568a14e290
-- title:
--   The coefficient field of an eigenform is a number field
-- statement:
--   Let $N>0$ and $k\ge2$, and let $f$ be a normalized algebraic cuspidal Hecke eigenform of level $N$ and weight $k$. Its coefficient field
--
--   $$
--   K_f=\mathbf Q\bigl(a_n(f),\varepsilon_f(a):n\ge0,\ a\in\mathbf Z/N\mathbf Z\bigr)
--   \subset\overline{\mathbf Q}
--   $$
--
--   is finite-dimensional over $\mathbf Q$. Thus all Fourier coefficients, Hecke eigenvalues, and nebentype values lie in one common number field, rather than merely being algebraic individually.
--
--   This provides the uniform coefficient field needed to choose a place above $p$ and form the residual Galois representation of $f$.
-- source:
--   The standard coefficient-field theorem for normalized cuspidal Hecke eigenforms; see Kriz--Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4, p. 27, https://arxiv.org/pdf/2310.20678

import Definitions.Def_MTT_EigenformCoefficientField

set_option autoImplicit false
noncomputable section

/-- The Fourier coefficients and nebentype values of an MTT eigenform generate
a single number field inside `MTT.Qbar`. -/
theorem MTT.Eigenform.coefficientField_finiteDimensional
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    FiniteDimensional ℚ f.coefficientField := by sorry
