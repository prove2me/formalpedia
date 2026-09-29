-- Prove2me | Theorems.Thm_Module_exists_surjective_linearMap_ext_of_exact_of_free
-- name    : Module.exists_surjective_linearMap_ext_of_exact_of_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6a4eb769-df8b-59ec-8599-bf8ebce316a4
-- title:
--   Cocycles of a dualised finite free complex compute Ext
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and let $K$ be a family of $R$-modules $K(i)$, indexed by $i\in\mathbb{N}$, each free over $R$, equipped with $R$-linear maps $\delta(i)\colon K(i)\to K(i+1)$ such that $\delta(i+1)\circ\delta(i)=0$ for all $i$, such that $\delta(0)$ is injective (every $z\in K(0)$ with $\delta(0)z=0$ vanishes), and such that for every $i<n$ the complex is exact at $K(i+1)$, i.e. every $z\in K(i+1)$ with $\delta(i+1)z=0$ lies in the range of $\delta(i)$. Let $M$ be any $R$-module, and put $Q:=K(n+1)/\operatorname{range}\delta(n)$, viewed as an object of `ModuleCat R`. The conclusion is a conjunction. First, there is an $R$-linear map $\pi$ from $\operatorname{Hom}_R(K(0),M)$ to $\operatorname{Ext}^{\,n+1}_R(Q,M)$ (Mathlib's `Abelian.Ext` in `ModuleCat R`, with its $R$-module structure) which is surjective and whose kernel is exactly the range of precomposition with $\delta(0)$, that is, the set of maps $\psi\circ\delta(0)$ with $\psi\in\operatorname{Hom}_R(K(1),M)$. Secondly, for every $i<n$ there is an $R$-linear map $\pi$ from the kernel of precomposition with $\delta(i)$ on $\operatorname{Hom}_R(K(i+1),M)$, i.e. from $\{\varphi:\varphi\circ\delta(i)=0\}$, to $\operatorname{Ext}^{\,n-i}_R(Q,M)$, which is surjective and satisfies $\pi\varphi=0$ if and only if $\varphi=\psi\circ\delta(i+1)$ for some $\psi\in\operatorname{Hom}_R(K(i+2),M)$.
--
--   This is the resolution-independence of $\operatorname{Ext}$ made explicit for a given finite free resolution: under the stated hypotheses $0\to K(0)\to\cdots\to K(n+1)\to Q\to 0$ is a free resolution of $Q$ of length $n+1$, and the statement identifies the cohomology of the dualised complex $\operatorname{Hom}_R(K^\bullet,M)$ with $\operatorname{Ext}^j_R(Q,M)$ for $1\le j\le n+1$, in the first-isomorphism-theorem form of a surjection together with a description of its kernel rather than as an isomorphism. It is used in the computation [`Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact`](thm.html#Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact), comparing lengths of a quotient by the image of the top differential with lengths attached to the dual complex.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_surjective_linearMap_ext_of_exact_of_free.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Module.exists_surjective_linearMap_ext_of_exact_of_free
    (R : Type u) [CommRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (M : Type u) [AddCommGroup M] [Module R M] :
    (∃ π : (K 0 →ₗ[R] M) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n + 1),
      Function.Surjective π ∧ LinearMap.ker π = LinearMap.range (LinearMap.lcomp R M (δ 0))) ∧
    ∀ i : ℕ, i < n →
      ∃ π : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)) →ₗ[R]
          Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n - i),
        Function.Surjective π ∧
          ∀ φ, π φ = 0 ↔ ∃ ψ : K (i + 2) →ₗ[R] M, (φ : K (i + 1) →ₗ[R] M) = ψ ∘ₗ δ (i + 1) := by sorry
