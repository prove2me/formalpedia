-- Prove2me | Theorems.Thm_MvPolynomial_IsWeightedHomogeneous_eq_monomial_of_unique_weight_tenProofs
-- name    : MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight_tenProofs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/f854bdeb-a07a-4236-91a2-1376537df777
-- title:
--   MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight_tenProofs
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open MvPolynomial MvPolynomial.IsWeightedHomogeneous

theorem MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight_tenProofs
    {σ R M : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {p : MvPolynomial σ R} {m : M} {d : σ →₀ ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m)
    (hunique : ∀ b : σ →₀ ℕ, Finsupp.weight w b = m → b = d) :
    p = MvPolynomial.monomial d (MvPolynomial.coeff d p) := by sorry
