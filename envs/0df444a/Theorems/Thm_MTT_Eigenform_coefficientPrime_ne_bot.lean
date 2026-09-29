-- Prove2me | Theorems.Thm_MTT_Eigenform_coefficientPrime_ne_bot
-- name    : MTT.Eigenform.coefficientPrime_ne_bot
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:35:26.181686+00:00
-- url     : https://prove2.me/theorems/31da2baf-82a1-4404-8629-e3e2e6849f39
-- title:
--   The selected coefficient prime is nonzero
-- statement:
--   The prime ideal of the eigenform coefficient field selected by a
--   $p$-adic embedding is not the zero ideal. Indeed, it contains the nonzero
--   rational integer $p$.
-- source:
--   The standard prime ideal selected by a p-adic embedding, together with the identity |p|_p < 1.

import Theorems.Thm_MTT_Eigenform_p_mem_coefficientPrime

set_option autoImplicit false
noncomputable section

/-- The coefficient-field prime selected by a `p`-adic embedding is nonzero. -/
theorem MTT.Eigenform.coefficientPrime_ne_bot
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientPrime ιp ≠ ⊥ := by
  sorry
