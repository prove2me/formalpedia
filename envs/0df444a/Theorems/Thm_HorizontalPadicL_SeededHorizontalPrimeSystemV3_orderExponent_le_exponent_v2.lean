-- Prove2me | Theorems.Thm_HorizontalPadicL_SeededHorizontalPrimeSystemV3_orderExponent_le_exponent_v2
-- name    : HorizontalPadicL.SeededHorizontalPrimeSystemV3.orderExponent_le_exponent_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:50:28.900798+00:00
-- url     : https://prove2.me/theorems/037c8a4e-0925-4a6c-a910-eaa2f7801ddf
-- title:
--   Orderly congruences bound local p-power exponents (inverse-seed convention)
-- statement:
--   Congruence modulo p^m implies that the maximal local p-power quotient
--   has exponent at least m.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.SeededHorizontalPrimeSystemV2.orderExponent_le_exponent`.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Congruence modulo p^m implies that the maximal local p-power quotient
has exponent at least m. -/
theorem SeededHorizontalPrimeSystemV3.orderExponent_le_exponent_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B) :
    ∀ n, L.orderExponent ≤ L.exponent n := by
  sorry

end HorizontalPadicL
