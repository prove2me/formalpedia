-- Prove2me | Theorems.Thm_LT_Artin_eq_artinFrob_of_isArithFrobAt
-- name    : LT.Artin.eq_artinFrob_of_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/fb4368a6-7859-590c-92d3-d37f238d657c
-- title:
--   Abelian case: any arithmetic Frobenius at Q is the Artin element
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an extension of $K$ which is Galois, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. a point of `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`. Assume the group $\mathrm{Gal}(M/K) = M \simeq_{\mathrm{alg}[K]} M$ has commutative multiplication (`IsMulCommutative`, so the extension is abelian). Let $\sigma \in \mathrm{Gal}(M/K)$ and let $Q$ be a prime ideal of $\mathcal{O}_M$, and suppose: $\sigma$ satisfies Mathlib's arithmetic-Frobenius predicate `IsArithFrobAt (𝓞 K) σ Q` relative to the base ring $\mathcal{O}_K$, that is, $\sigma$ stabilises $Q$ and $\sigma(x) \equiv x^{\,|\mathcal{O}_K/(Q \cap \mathcal{O}_K)|} \pmod Q$ for all $x \in \mathcal{O}_M$; the prime of $\mathcal{O}_K$ lying under $Q$ is $v$, i.e. $Q \cap \mathcal{O}_K = v$ as ideals; and the inertia subgroup of $Q$ inside $\mathrm{Gal}(M/K)$ is trivial. The conclusion is that $\sigma$ coincides with [`LanglandsTunnell.P2.Artin.artinFrob K M v`](def/LanglandsTunnell_ArtinFrobenius.html#L72), which is by definition the arithmetic Frobenius `arithFrobAt (𝓞 K) (M ≃ₐ[K] M)` computed at one fixed, chosen prime `primeAbove K M v` of $\mathcal{O}_M$ above $v$.
--
--   This is the uniqueness and choice-independence of the Frobenius substitution at a prime unramified in an abelian extension: in the abelian case the Artin symbol attached to $v$ is computed by any element satisfying the Frobenius congruence at any prime above $v$ with trivial inertia. It is used in the construction and manipulation of the idelic Artin map, e.g. in [`M4aHerbrand.restrictNormalHom_idelicArtinMap_eq`](thm.html#M4aHerbrand.restrictNormalHom_idelicArtinMap_eq), [`M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt`](thm.html#M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt) and [`NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj`](thm.html#NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_Artin_eq_artinFrob_of_isArithFrobAt.lean

import Definitions.Def_LanglandsTunnell_ArtinFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.Artin.eq_artinFrob_of_isArithFrobAt
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v := by sorry
