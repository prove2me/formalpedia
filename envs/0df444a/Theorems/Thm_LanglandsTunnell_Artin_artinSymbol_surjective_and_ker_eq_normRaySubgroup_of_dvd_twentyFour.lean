-- Prove2me | Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
-- name    : LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/8c02fb2b-5663-5a8c-a653-28e259115a60
-- title:
--   Artin reciprocity at an admissible modulus, exponent dividing 24
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois and with abelian Galois group $\mathrm{Gal}(L/K) = L \simeq_{\mathrm{alg}[K]} L$ (commutativity being assumed as `IsMulCommutative`). Let $\ell$ be a prime and $k$ a natural number such that $x^{\ell^k} = 1$ for every $x \in \mathrm{Gal}(L/K)$, and assume $\ell^k \mid 24$. Let $\mathfrak f$ be an ideal of $\mathcal O_K$ that is admissible for $L/K$ in the sense of `IsAdmissibleModulus`: $\mathfrak f \neq \bot$, and for every height-one prime $v$ of $\mathcal O_K$ whose chosen prime `primeAbove K L v` of $\mathcal O_L$ has nontrivial inertia subgroup in $\mathrm{Gal}(L/K)$, one has $v^{\,4e_v(2)+2e_v(3)+1} \mid \mathfrak f$, where $e_v(p)$ denotes `Ideal.ramificationIdx'` of the ideal $p\mathbb Z$ at $v$. The conclusion is a conjunction about the Artin symbol `artinSymbol K L 𝔣`, the homomorphism from the group of units of fractional ideals of $K$ coprime to $\mathfrak f$ (those whose `FractionalIdeal.count` vanishes at every prime dividing $\mathfrak f$) to $\mathrm{Gal}(L/K)$ obtained from the arithmetic Frobenius `artinFrob K L v` at the chosen prime above each $v$: it is surjective, and its kernel equals the norm-ray subgroup `normRaySubgroup K L 𝔣`, the join inside the coprime-to-$\mathfrak f$ group of the narrow ray subgroup (the closure of `narrowRaySet K 𝔣`) with the image of the relative norm `relNormCTM` from the fractional ideals of $L$ coprime to the extended modulus.
--
--   This is Artin's reciprocity law in ray-class form — the Artin map modulo an admissible modulus is surjective with kernel the norm-ray subgroup — restricted to abelian extensions whose exponent is a prime power dividing $24$, the admissibility condition on $\mathfrak f$ being the explicit depth $4e_v(2)+2e_v(3)+1$ at ramified primes. It is the ideal-theoretic input to the construction of the idelic Artin map in [`NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour`](thm.html#NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour), used in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell.P2.Artin

universe u v

theorem LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (hk : ℓ ^ k ∣ 24) :
    Function.Surjective (artinSymbol K L 𝔣) ∧ (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by sorry
