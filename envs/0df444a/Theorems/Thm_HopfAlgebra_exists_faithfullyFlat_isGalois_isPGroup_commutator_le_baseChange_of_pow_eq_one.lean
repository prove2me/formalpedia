-- Prove2me | Theorems.Thm_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
-- name    : HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/78096f93-007b-50bf-a273-f1e029f6dca1
-- title:
--   Faithfully flat base change making Galois abelian-by-p
-- statement:
--   Let $R$ be a discrete valuation domain, $p$ a prime number which is irreducible in $R$ (a uniformiser), and $H$ a commutative, cocommutative Hopf algebra over $R$ that is finite and flat as an $R$-module. Assume for some $n$ that for every commutative $R$-algebra $T$ the group $\mathrm{WithConv}(H \to_{\mathrm{alg}} T)$ of $R$-algebra maps $H \to T$ under convolution satisfies $f^{p^n} = 1$ for all $f$. Then there exist a discrete valuation domain $R_2$, an $R$-algebra structure on $R_2$ making it faithfully flat over $R$, and a fraction field $K_2$ of $R_2$, such that $p$ is irreducible in $R_2$ and, for some $N \in \mathbb{N}$: (i) for every $s$ with $0 < s \le N$ and every finite field $F$ with $\#F = p^s$, the element $p^s - 1$ is a unit of $R_2$ and there are a group homomorphism $\chi : F^\times \to R_2^\times$ and a ring homomorphism $\iota : F \to R_2/\mathfrak{m}_2$ with $\chi(l) \bmod \mathfrak{m}_2 = \iota(l)$ for all $l \in F^\times$; and, writing $A_2 = K_2 \otimes_{R_2} (R_2 \otimes_R H)$ and $V$ for the convolution group of $K_2$-algebra maps $A_2 \to \overline{K_2}$, (ii) $V$ is finite, (iii) the $\overline{K_2}$-algebra map $\overline{K_2} \otimes_{K_2} A_2 \to \overline{K_2}^V$ obtained by lifting the structure map together with evaluation at the points of $V$ is bijective, (iv) $\#V \le p^N$, (v) $\nu^{p^n} = 1$ for every $\nu \in V$, and (vi) there is a finite Galois intermediate field $L$ of $\overline{K_2}/K_2$ such that every $K_2$-algebra map $A_2 \to \overline{K_2}$ takes values in $L$, together with a normal subgroup $P \le \mathrm{Gal}(L/K_2)$ which is a $p$-group and contains every commutator $a^{-1}b^{-1}ab$, so that $\mathrm{Gal}(L/K_2)/P$ is abelian.
--
--   This is the base-change input to Raynaud's dévissage of finite flat commutative group schemes killed by $p^n$ over a discrete valuation ring with uniformiser $p$: after a faithfully flat extension of the base one may assume the residue field contains the needed finite fields with Teichmüller lifts of their multiplicative characters, that the generic-fibre points are finite in number and rational over a finite Galois extension $L/K_2$, and that $\mathrm{Gal}(L/K_2)$ is an extension of an abelian group by a normal $p$-subgroup (wild inertia). It is used to produce the filtration by $F$-vector space schemes in [`HopfAlgebra.exists_faithfullyFlat_hasFVectDevissage_baseChange_of_pow_eq_one`](thm.html#HopfAlgebra.exists_faithfullyFlat_hasFVectDevissage_baseChange_of_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_faithfullyFlat_isGalois_isPGroup_commutator_le_baseChange_of_pow_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (n : ℕ) (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂) (_ : Algebra R R₂)
      (_ : Module.FaithfullyFlat R R₂) (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂),
      Irreducible (p : R₂) ∧
      ∃ N : ℕ,
        (∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
          IsUnit ((p ^ s : R₂) - 1) ∧
            ∃ (χ : Fˣ →* R₂ˣ) (ι : F →+* IsLocalRing.ResidueField R₂),
              ∀ l : Fˣ, IsLocalRing.residue R₂ (χ l : R₂) = ι l) ∧
        Finite (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure K₂) (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂))
            (Pi.algHom K₂ _
              fun ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) =>
                (WithConv.ofConv ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure K₂ ⊗[K₂] (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[AlgebraicClosure K₂]
              (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) → AlgebraicClosure K₂)) ∧
        Nat.card (WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂)) ≤ p ^ N ∧
        (∀ ν : WithConv ((K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂), ν ^ p ^ n = 1) ∧
        ∃ (L : IntermediateField K₂ (AlgebraicClosure K₂)) (_ : FiniteDimensional K₂ L) (_ : IsGalois K₂ L),
          (∀ (ν : (K₂ ⊗[R₂] (R₂ ⊗[R] H)) →ₐ[K₂] AlgebraicClosure K₂) (a : (K₂ ⊗[R₂] (R₂ ⊗[R] H))), ν a ∈ L) ∧
          ∃ P : Subgroup (L ≃ₐ[K₂] L), P.Normal ∧ IsPGroup p ↥P ∧
            ∀ a b : (L ≃ₐ[K₂] L), a⁻¹ * b⁻¹ * a * b ∈ P := by sorry
