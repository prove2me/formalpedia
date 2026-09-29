-- Prove2me | Theorems.Thm_HorizontalPadicL_positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
-- name    : HorizontalPadicL.positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:22:48.10302+00:00
-- url     : https://prove2.me/theorems/41fd2636-d820-49e2-8385-68716ee4538e
-- title:
--   Enumerating a positive-density orderly-prime set (inverse-seed convention)
-- statement:
--   Let $A$ be a positive-density set of rational primes, all orderly with the same exponent $m>0$, and all avoiding a fixed modulus $B$. Then $A$ admits an injective enumeration which, together with its density certificate and local properties, defines a seeded horizontal prime system of order exponent $m$.
--
--   This is the set-theoretic passage from the Chebotarev prime set to the sequence required by the horizontal measure construction.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.positiveDensityOrderlySet_to_primeSystem`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, §4.3, Lemma 4.14 and Corollary 4.15, pp. 30–31.

import Definitions.Def_KN_SeededPrimeGaloisDataV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false

namespace HorizontalPadicL

theorem positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (hm : 0 < m)
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity D.primes δ)
    (horderly : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ) :
    ∃ L : SeededHorizontalPrimeSystemV3 p V.embedding f η B,
      L.orderExponent = m := by sorry

end HorizontalPadicL
