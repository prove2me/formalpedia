-- Prove2me | Theorems.Thm_MTT_numberField_coefficientField
-- name    : MTT.numberField_coefficientField
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T08:20:24.338829+00:00
-- url     : https://prove2.me/theorems/8c4d2529-1d78-4052-9180-85a6dc276fb0
-- title:
--   The coefficient field of an eigenform is a number field
-- statement:
--   Let $f$ be an MTT eigenform of positive level $N$ and weight $k \ge 2$. Its coefficient field $K_f$, generated over $\mathbb Q$ by all Fourier coefficients and all values of the nebentype, is a number field:
--   $$
--   [K_f : \mathbb Q] < \infty.
--   $$
--   This packages finite-dimensionality into Mathlib's standard NumberField predicate, making the arithmetic of its integer ring and residue fields directly available.
-- source:
--   Standard consequence of finite-dimensionality of the coefficient field over ℚ; see Diamond–Shurman, A First Course in Modular Forms, §5.8.

import Definitions.Def_MTT_EigenformCoefficientField
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false
noncomputable section

theorem MTT.numberField_coefficientField
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := by sorry
