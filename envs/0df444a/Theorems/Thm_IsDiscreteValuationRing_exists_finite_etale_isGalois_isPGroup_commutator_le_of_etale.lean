-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
-- name    : IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/acff95bd-2d4b-52bd-b6e5-7c1f7d39266d
-- title:
--   Unramified base change making Galois act abelian-by-p
-- statement:
--   Let $R_1$ be a discrete valuation domain, complete with respect to its maximal ideal, let $K_1$ be a field of characteristic $0$ that is a fraction field of $R_1$, let $p$ be a prime such that $p$ is irreducible in $R_1$ (i.e. a uniformiser), let $N$ be a natural number, and let $B_1$ be a commutative $K_1$-algebra that is finite as a $K_1$-module and étale over $K_1$. The assertion is that there exist a discrete valuation domain $R_2$, in the same universe as $R_1$, with an $R_1$-algebra structure making $R_2$ finite, free and faithfully flat as an $R_1$-module, and a field $K_2$ which is a fraction field of $R_2$ and carries compatible $K_1$- and $R_1$-algebra structures (the towers $R_1 \to R_2 \to K_2$ and $R_1 \to K_1 \to K_2$ agreeing), such that: $p$ is irreducible in $R_2$; the structure map $R_1 \to R_2$ is a local homomorphism; for every $s$ with $0 < s \le N$ and every finite field $F$ with $\#F = p^s$, the element $p^s - 1$ is a unit of $R_2$ and there are a group homomorphism $\chi \colon F^{\times} \to R_2^{\times}$ and a ring homomorphism $\iota \colon F \to$ the residue field of $R_2$ with $\chi(l)$ reducing to $\iota(l)$ for all $l \in F^{\times}$ (Teichmüller data); and there is an intermediate field $L$ of $\mathrm{AlgebraicClosure}\,K_2$ over $K_2$, finite-dimensional and Galois over $K_2$, such that every $K_2$-algebra homomorphism $\nu \colon K_2 \otimes_{K_1} B_1 \to \mathrm{AlgebraicClosure}\,K_2$ takes all its values in $L$, and a normal subgroup $P$ of $\mathrm{Gal}(L/K_2)$ which is a $p$-group and contains $a^{-1}b^{-1}ab$ for all $a, b \in \mathrm{Gal}(L/K_2)$, so that $\mathrm{Gal}(L/K_2)$ is abelian-by-$p$. Despite the name, the conclusion asserts only that $R_2$ is finite, free and faithfully flat over $R_1$ with local structure map, not that it is étale over $R_1$, and it does not assert completeness of $R_2$.
--
--   This is the field-theoretic core of the reduction, in Raynaud's study of group schemes of type $(p,\dots,p)$, to the situation where the Galois group acting on the relevant points is inertia-like: after an unramified base extension of the complete base one may adjoin the geometric points of a finite étale algebra and arrange that wild inertia is a normal $p$-subgroup with abelian quotient, while simultaneously providing Teichmüller characters for the finite fields of order $p^s$, $s \le N$. It is used in the proof of [`HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one`](thm.html#HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale
    {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁]
    (K₁ : Type u) [Field K₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁] [CharZero K₁]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R₁)) (N : ℕ)
    (B₁ : Type v) [CommRing B₁] [Algebra K₁ B₁] [Module.Finite K₁ B₁] [Algebra.Etale K₁ B₁] :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂)
      (_ : Algebra R₁ R₂) (_ : Module.Finite R₁ R₂) (_ : Module.Free R₁ R₂) (_ : Module.FaithfullyFlat R₁ R₂)
      (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂)
      (_ : Algebra K₁ K₂) (_ : Algebra R₁ K₂) (_ : IsScalarTower R₁ R₂ K₂) (_ : IsScalarTower R₁ K₁ K₂),
      Irreducible (p : R₂) ∧ IsLocalHom (algebraMap R₁ R₂) ∧
      (∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
        IsUnit ((p ^ s : R₂) - 1) ∧
          ∃ (χ : Fˣ →* R₂ˣ) (ι : F →+* IsLocalRing.ResidueField R₂),
            ∀ l : Fˣ, IsLocalRing.residue R₂ (χ l : R₂) = ι l) ∧
      ∃ (L : IntermediateField K₂ (AlgebraicClosure K₂)) (_ : FiniteDimensional K₂ L) (_ : IsGalois K₂ L),
        (∀ (ν : K₂ ⊗[K₁] B₁ →ₐ[K₂] AlgebraicClosure K₂) (b : K₂ ⊗[K₁] B₁), ν b ∈ L) ∧
        ∃ P : Subgroup (L ≃ₐ[K₂] L), P.Normal ∧ IsPGroup p ↥P ∧
          ∀ a b : (L ≃ₐ[K₂] L), a⁻¹ * b⁻¹ * a * b ∈ P := by sorry
