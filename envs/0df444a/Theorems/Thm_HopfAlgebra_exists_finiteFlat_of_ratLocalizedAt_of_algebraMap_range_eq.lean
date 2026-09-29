-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq
-- name    : HopfAlgebra.exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b12f47c3-eb33-53c3-bd6e-100c58458214
-- title:
--   Transport of a finite flat Hopf model along R ≅ ℤ₍ₚ₎
-- statement:
--   Let $R$ be a commutative domain endowed with a $\mathbb{Q}$-algebra structure making $\mathbb{Q}$ its fraction field, together with a $\overline{\mathbb{Q}}$-algebra structure (for $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`) compatible with the map $R \to \mathbb{Q}$ in the sense of a scalar tower, and let $p$ be a prime. Assume that the image of $\operatorname{algebraMap} R\,\mathbb{Q}$ is exactly the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $N$ be an additive commutative group carrying a distributive action of $G = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and let $H$ be a commutative ring which is a Hopf algebra over that subring, finite and flat as a module over it and cocommutative as a coalgebra, and suppose given a bijection $e_H$ from `WithConv` applied to the set of subring-algebra maps $H \to \overline{\mathbb{Q}}$ onto $N$ such that $e_H(f \cdot g) = e_H f + e_H g$ for all $f, g$, and such that whenever $\sigma \in G$ and $g$ satisfies $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e_H g = \sigma \cdot e_H f$. The conclusion asserts the existence of a type $H'$ with a commutative ring structure and a Hopf algebra structure over $R$ which is finite, flat and cocommutative over $R$, together with a bijection $e'$ from `WithConv` applied to the $R$-algebra maps $H' \to \overline{\mathbb{Q}}$ onto the same $N$, satisfying the same two conditions ($e'(f\cdot g) = e' f + e' g$, and $\sigma$-equivariance in the above sense).
--
--   This is a restriction-of-scalars step: a finite flat cocommutative Hopf algebra over $\mathbb{Z}_{(p)}$, whose $\overline{\mathbb{Q}}$-points realise a given Galois module $N$, is transported to any domain $R$ with fraction field $\mathbb{Q}$ whose image in $\mathbb{Q}$ is $\mathbb{Z}_{(p)}$, the Galois-equivariant identification of points being preserved. It feeds the construction of finite flat models over discrete valuation rings used in [`HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible`](thm.html#HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_of_ratLocalizedAt_of_algebraMap_range_eq
    (R : Type) [CommRing R] [IsDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra R (AlgebraicClosure ℚ)] [IsScalarTower R ℚ (AlgebraicClosure ℚ)]
    (p : ℕ) [Fact p.Prime]
    (hrange : (algebraMap R ℚ).range = GaloisRep.ratLocalizedAt p)
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    (hHfin : Module.Finite (GaloisRep.ratLocalizedAt p) H)
    (hHflat : Module.Flat (GaloisRep.ratLocalizedAt p) H)
    (hHcocomm : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H)
    (eH : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by sorry
