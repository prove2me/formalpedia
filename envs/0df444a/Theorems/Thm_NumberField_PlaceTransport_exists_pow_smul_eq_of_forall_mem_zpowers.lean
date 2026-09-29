-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers
-- name    : NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/805032b7-ee48-547c-affd-b8ebc554c9a0
-- title:
--   Cyclic Galois group moves places above v by a natural power
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ a $K$-algebra such that $L/K$ is Galois, and let $\sigma$ be an element of $\mathrm{Gal}(L/K) = L \simeq_{\text{alg}[K]} L$. Assume that every $\tau \in \mathrm{Gal}(L/K)$ lies in `Subgroup.zpowers σ`, i.e. $\tau = \sigma^{k}$ for some $k \in \mathbb{Z}$, so that the Galois group is cyclic with generator $\sigma$. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $w, w'$ be two elements of `v.Extension (𝓞 L)`, that is, height-one primes of $\mathcal{O}_L$ whose contraction along $\mathcal{O}_K \to \mathcal{O}_L$ (their `under (𝓞 K)`) equals $v$. The conclusion is the existence of a natural number $n$ with $(\sigma^{n}) \cdot w.1 = w'.1$, where the underlying height-one primes of $\mathcal{O}_L$ are acted on by the scoped place-transport action of $\mathrm{Gal}(L/K)$, under which the ideal of $\sigma \cdot w$ is the image of the ideal of $w$ under $\sigma$. Note that the exponent is asserted to be a natural number, not merely an integer.
--
--   This is the transitivity of the Galois action on the primes of $\mathcal{O}_L$ above a fixed prime of $\mathcal{O}_K$, in the form needed when the Galois group is cyclic: a single non-negative power of the chosen generator already carries one place above $v$ to any other. It is used in the automorphic-form part of the development, in statements about semi-local unit components, twisted Bruhat data, and the decomposition of adelic completions under a cyclic Galois group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers.lean

import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w w' : v.Extension (𝓞 L)) :
    ∃ n : ℕ, (σ ^ n) • w.1 = w'.1 := by sorry
