-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible
-- name    : HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/1b2d142b-639c-5155-9af4-31f002e804df
-- title:
--   Finite flat Hopf model over a DVR with fraction field ℚ
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, equipped with an algebra structure over $\mathbb{Q}$ exhibiting $\mathbb{Q}$ as its fraction field, together with an $R$-algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` compatible with the tower $R \to \mathbb{Q} \to \overline{\mathbb{Q}}$. Let $p$ be a natural number, prime by a `Fact` instance, whose image in $R$ is irreducible. Let $N$ be an additive commutative group carrying a distributive multiplicative action of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Write $\mathbb{Z}_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring with a Hopf algebra structure over $\mathbb{Z}_{(p)}$ which is finite and flat as a $\mathbb{Z}_{(p)}$-module and whose comultiplication is cocommutative, and suppose given a bijection $e_H$ from the monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ onto $N$ which carries the multiplication of that monoid to addition in $N$ and which is Galois-equivariant in the sense that $e_H(g) = \sigma \cdot e_H(f)$ whenever $g(h) = \sigma(f(h))$ for all $h \in H$. Then there exists a type $H'$ with a commutative ring structure and a Hopf algebra structure over $R$ which is finite and flat as an $R$-module and cocommutative, together with a bijection $e'$ from `WithConv` on the $R$-algebra homomorphisms $H' \to \overline{\mathbb{Q}}$ onto $N$ enjoying the same two properties: multiplicativity-to-additivity and the same Galois equivariance.
--
--   This is the transport step that frees the finite flat cocommutative Hopf model (the coordinate ring of a finite flat group scheme, with its $\overline{\mathbb{Q}}$-points identified Galois-equivariantly with $N$) from the concrete base ring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$, allowing any discrete valuation ring with fraction field $\mathbb{Q}$ in which $p$ is a uniformiser to serve as base. It is used in turn to obtain such models over bases presented differently, as in [`HopfAlgebra.exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along`](thm.html#HopfAlgebra.exists_finiteFlat_dvr_of_padicInt_of_withConv_equiv_along).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra R (AlgebraicClosure ℚ)] [IsScalarTower R ℚ (AlgebraicClosure ℚ)]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R))
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
