-- Prove2me | Theorems.Thm_MTT_Eigenform_nebentype_mem_ringOfIntegers
-- name    : MTT.Eigenform.nebentype_mem_ringOfIntegers
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T07:00:59.98577+00:00
-- url     : https://prove2.me/theorems/c936cb93-837c-4aa5-b2ea-4546b6f84fa1
-- title:
--   Nebentype values lie in the ring of integers of the coefficient field
-- statement:
--   Let $f$ be an MTT eigenform with coefficient field $K_f$ and nebentype $\varepsilon_f$. Every value of the nebentype, viewed as an element of $K_f$, lies in its ring of integers:
--
--   $$
--   \varepsilon_f(a)\in\mathcal O_{K_f}
--   \qquad(a\in\mathbf Z/N\mathbf Z).
--   $$
--
--   Nonzero nebentype values are roots of unity; the possible zero values are integral as well.
-- source:
--   Standard algebraicity and integrality properties of normalized cuspidal Hecke eigenforms; coefficient-field notation as in Kriz--Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4, p. 27, https://arxiv.org/pdf/2310.20678

import Definitions.Def_MTT_EigenformCoefficientField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

/-- Every nebentype value, regarded as an element of the coefficient field,
belongs to its ring of integers. -/
theorem MTT.Eigenform.nebentype_mem_ringOfIntegers
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι)
    (a : ZMod N) :
    (⟨f.epsilon a, f.nebentype_mem_coefficientField a⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by sorry
