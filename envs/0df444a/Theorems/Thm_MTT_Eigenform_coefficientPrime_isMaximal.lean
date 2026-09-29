-- Prove2me | Theorems.Thm_MTT_Eigenform_coefficientPrime_isMaximal
-- name    : MTT.Eigenform.coefficientPrime_isMaximal
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:42:33.773707+00:00
-- url     : https://prove2.me/theorems/50aa5bf2-15e7-4738-b986-9b482f3505e6
-- title:
--   The coefficient prime selected by a p-adic embedding is maximal
-- statement:
--   For an eigenform of positive level and weight at least two, the
--   nonzero prime ideal of its coefficient ring selected by a $p$-adic embedding
--   is maximal.
-- source:
--   The ring of integers of a number field is a Dedekind domain, in which every nonzero prime ideal is maximal.

import Theorems.Thm_MTT_Eigenform_coefficientPrime_isPrime
import Theorems.Thm_MTT_Eigenform_coefficientPrime_ne_bot
import Theorems.Thm_MTT_numberField_coefficientField
import Mathlib.RingTheory.DedekindDomain.Basic

set_option autoImplicit false
noncomputable section

open NumberField

/-- The prime selected by a `p`-adic embedding is a maximal ideal of the
integer ring of the coefficient field. -/
theorem MTT.Eigenform.coefficientPrime_isMaximal
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsMaximal := by
  sorry
