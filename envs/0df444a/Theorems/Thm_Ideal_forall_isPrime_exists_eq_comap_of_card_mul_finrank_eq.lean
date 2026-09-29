-- Prove2me | Theorems.Thm_Ideal_forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq
-- name    : Ideal.forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/5ff7ad11-d396-56f0-9615-9568656d5696
-- title:
--   Automorphic translates of a prime exhaust the primes
-- statement:
--   Let $F$ be a field and $R$ a commutative $F$-algebra which is finite as an $F$-module and reduced. Let $\mathfrak p_0$ be a prime ideal of $R$, let $I$ be a finite type, and let $e : I \to (R \simeq_{F\text{-alg}} R)$ be a family of $F$-algebra automorphisms of $R$. Assume two hypotheses: (i) the map $i \mapsto e_i^{-1}(\mathfrak p_0)$, formally the contraction `Ideal.comap` of $\mathfrak p_0$ along the ring homomorphism underlying $e_i$, is injective in the sense that equality of these contractions for $i$ and $i'$ forces $i = i'$; and (ii) the numerical identity $\#I \cdot \dim_F (R/\mathfrak p_0) = \dim_F R$ holds, where $\dim_F$ denotes `Module.finrank`. The conclusion is that every prime ideal $\mathfrak p$ of $R$ is of this form: there exists $i \in I$ with $\mathfrak p$ equal to the contraction of $\mathfrak p_0$ along $e_i$.
--
--   This is an exhaustion criterion: a family of automorphic translates of a single prime, pairwise distinct and of the expected total residue dimension, already accounts for all primes of $R$, hence for all irreducible components of $\operatorname{Spec} R$. It is used in the analysis of the components of fibre products attached to modular curves of full level, where the translates come from relabelling automorphisms and the dimension count is supplied by a degree and a rank computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (𝔭₀ : Ideal R) (h𝔭₀ : 𝔭₀.IsPrime)
    (I : Type) [Fintype I] (e : I → (R ≃ₐ[F] R))
    (hinj : ∀ i i' : I, Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ = Ideal.comap ((e i' : R →ₐ[F] R) : R →+* R) 𝔭₀ → i = i')
    (hcount : Fintype.card I * Module.finrank F (R ⧸ 𝔭₀) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ i : I, 𝔭 = Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ := by sorry
