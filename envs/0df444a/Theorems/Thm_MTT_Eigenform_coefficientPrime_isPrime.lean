-- Prove2me | Theorems.Thm_MTT_Eigenform_coefficientPrime_isPrime
-- name    : MTT.Eigenform.coefficientPrime_isPrime
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:41:31.656576+00:00
-- url     : https://prove2.me/theorems/bf91feb0-0052-4fd0-bbfb-414f22f43b6b
-- title:
--   The coefficient prime selected by a p-adic embedding is prime
-- statement:
--   The ideal of the eigenform coefficient ring selected by an embedding
--   into $\mathbf C_p$ is a prime ideal.
-- source:
--   Prime ideals pull back along ring homomorphisms; the maximal ideal of the valuation ring of C_p is prime.

import Definitions.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

/-- The prime selected by a `p`-adic embedding is a prime ideal. -/
theorem MTT.Eigenform.coefficientPrime_isPrime
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := by
  sorry
