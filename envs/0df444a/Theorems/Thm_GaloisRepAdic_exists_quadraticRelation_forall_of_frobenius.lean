-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius
-- name    : GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/6afb4853-2fa5-55db-812e-03090be835cb
-- title:
--   Chebotarev spreading of a Frobenius quadratic relation
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation domain that is complete for the adic topology of its maximal ideal, and let $p$ be a prime with $p \in \mathfrak m_{\mathcal O}$. Let $R$ be a local commutative $\mathcal O$-algebra, finite as an $\mathcal O$-module, whose structure map $\mathcal O \to R$ is a local homomorphism. Let $\rho$ be a [`GaloisRepAdic R`](def/GaloisRep_Adic.html#L16), that is: a free $R$-module $V$ of rank $2$, finite over $R$, together with a monoid homomorphism $\rho.\rho$ from $G = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_R V$ which is $\mathfrak m_R$-adically continuous in the sense that for every $n$ there is a finite intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ with $\rho.\rho(\sigma)v - v \in \mathfrak m_R^n \cdot V$ for all $v$ and all $\sigma$ fixing $F$ pointwise; $\rho.trace\,\sigma$ denotes the $R$-linear trace of $\rho.\rho(\sigma)$ on $V$. Let $Y$ carry compatible $R$- and $\mathcal O$-module structures (a scalar tower), be finite over $\mathcal O$, and let $\rho_Y : G \to \mathrm{End}_R Y$ be a monoid homomorphism such that for every $n$ there is a finite intermediate field $F$ with $\rho_Y(\sigma)y - y \in (\mathrm{span}\{p\}^n)\cdot Y$ for all $y \in Y$ and all $\sigma$ fixing $F$ pointwise. Let $L$ be a nonzero natural number and $D : (\mathbb Z/L)^\times \to \mathrm{End}_R Y$ a monoid homomorphism whose values commute with every $\rho_Y(\sigma)$. Assume there is a finite set $S_0$ of natural numbers such that for every prime $\ell \notin S_0$ with $\ell \nmid L$ and $\ell \neq p$, every valuation subring $P$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $P$, and every $\sigma$ that is a Frobenius at $\ell$ for $P$ (i.e. $\sigma$ lies in the decomposition subgroup of $P$ over $\mathbb Q$ and acts on the residue field of $P$ as $x \mapsto x^{\ell}$), one has $$\rho_Y(\sigma)^2 - \rho.trace(\sigma)\cdot\rho_Y(\sigma) + \ell\cdot D\big([\ell] \in (\mathbb Z/L)^\times\big) = 0 .$$ Then there exist monoid homomorphisms $c : G \to R^\times$ and $\chi : G \to (\mathbb Z/L)^\times$ such that $\rho_Y(\sigma)^2 - \rho.trace(\sigma)\cdot\rho_Y(\sigma) + c(\sigma)\cdot D(\chi(\sigma)) = 0$ holds for every $\sigma \in G$.
--
--   This is the passage from an Eichler–Shimura type quadratic relation, known at Frobenius elements outside a finite set of primes, to the same relation at every element of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, the characters $c$ and $\chi$ playing the roles of the $p$-adic and mod-$L$ cyclotomic characters; density of Frobenius classes and adic continuity of all the ingredients are what make the spreading possible. It is used in the construction of Galois actions on Hecke lattices, namely by the surjectivity statement for products of torsion quotients of Hecke rings at levels prime to a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R))
    (ρ : GaloisRepAdic R)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y] [Module.Finite 𝒪 Y]
    (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R Y)
    (hcont : ∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)))
    (L : ℕ) [NeZero L] (D : (ZMod L)ˣ →* Module.End R Y)
    (hD : ∀ (u : (ZMod L)ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), D u * ρY σ = ρY σ * D u)
    (S₀ : Finset ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ∀ (hℓL : ¬ ℓ ∣ L), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ.trace σ) • ρY σ
            + (ℓ : R) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) :
    ∃ (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ)
      (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((c σ : Rˣ) : R) • D (χ σ) = 0 := by sorry
