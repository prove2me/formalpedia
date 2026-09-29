-- Prove2me | Theorems.Thm_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
-- name    : NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/96979dc9-d73b-5b84-a211-7258cb942973
-- title:
--   Product formula over any sufficiently large finite set of primes
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` structure, so of finite degree over $\mathbb{Q}$ with ring of integers $\mathcal{O}_K$) and let $x \in K$ with $x \neq 0$. The assertion is the existence of a finite set $T_0$ of height-one primes of $\mathcal{O}_K$ (elements of `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`, i.e. nonzero prime ideals) with the following property: for every finite set $T$ of height-one primes of $\mathcal{O}_K$ with $T_0 \subseteq T$, the product of the archimedean contributions $\prod_{v} v(x)^{\,\mathrm{mult}(v)}$, taken over all infinite places $v$ of $K$ and with $\mathrm{mult}(v)$ the local multiplicity ($1$ at a real place, $2$ at a complex place), multiplied by the finite product $\prod_{v \in T} \lVert x \rVert_{v}$ of the norms of the images of $x$ under the structure maps $K \to K_v$ into the $v$-adic completions, equals $1$. Thus the classical product formula is packaged so that the infinite product over the finite places is replaced by a product over an arbitrary finite set of primes containing a fixed finite exceptional set, the omitted factors being equal to $1$.
--
--   This is the product formula for a number field, reshaped for use in computations where the finite part must appear as a genuine `Finset` product over a set of primes that may be enlarged at will. It is used in the adelic volume computations for automorphic forms, where the archimedean and finite normalising factors attached to a nonzero scalar have to cancel against each other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
    (K : Type) [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ T : Finset (HeightOneSpectrum (𝓞 K)), T₀ ⊆ T →
      (∏ v : InfinitePlace K, v x ^ v.mult) *
          ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) x‖ = 1 := by sorry
