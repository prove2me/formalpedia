-- Prove2me | Theorems.Thm_MTT_Eigenform_p_mem_coefficientPrime
-- name    : MTT.Eigenform.p_mem_coefficientPrime
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:34:23.158873+00:00
-- url     : https://prove2.me/theorems/b8db3c01-54d3-4082-897d-a1bb59c2ad90
-- title:
--   The rational prime belongs to the selected coefficient prime
-- statement:
--   Let $f$ be an MTT eigenform and let
--   $\iota_p:\overline{\mathbf Q}\hookrightarrow\mathbf C_p$ select the prime
--   $\lambda_{\iota_p}$ of its coefficient field. Then the rational integer $p$
--   belongs to $\lambda_{\iota_p}$.
-- source:
--   The standard prime ideal selected by a p-adic embedding, together with the identity |p|_p < 1.

import Definitions.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

open NumberField

/-- The rational prime `p` belongs to the coefficient-field prime selected by
a `p`-adic embedding. -/
theorem MTT.Eigenform.p_mem_coefficientPrime
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (p : 𝓞 f.coefficientField) ∈ f.coefficientPrime ιp := by
  sorry
