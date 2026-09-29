-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
-- name    : HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/6771338f-1cdb-5bc1-aee2-ad9c775268bd
-- title:
--   Schematic closure of a Galois-stable monoid of ℚ̄-points
-- statement:
--   Let $R$ be a principal ideal domain equipped with an $R$-algebra structure on $\mathbb{Q}$ exhibiting $\mathbb{Q}$ as its fraction field, and let $H$ be a commutative ring which is a Hopf algebra over $R$, finite and flat as an $R$-module, whose comultiplication is cocommutative. Write $\overline{\mathbb{Q}}$ for `AlgebraicClosure ℚ`, an $R$-algebra through $\mathbb{Q}$, and let `WithConv (H →ₐ[R] AlgebraicClosure ℚ)` denote the set of $R$-algebra maps $H \to \overline{\mathbb{Q}}$ with its convolution monoid structure. Let $\Gamma$ be a submonoid of this convolution monoid which is Galois-stable in the following sense: for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $\nu \in \Gamma$, the composite of $\nu$ with $\sigma$ (viewed again as an element of the convolution monoid) lies in $\Gamma$. Then there exist a type $H'$ carrying a commutative ring structure and an $R$-Hopf algebra structure, and a bialgebra homomorphism $\pi : H \to H'$ over $R$, such that $\pi$ is surjective, $H'$ is finite and flat as an $R$-module with cocommutative comultiplication, the ideal $\ker \pi$ equals the infimum $\bigwedge_{\nu \in \Gamma} \ker \nu$ of the kernels of the members of $\Gamma$, and, for every commutative $R$-algebra $T$, every injective $R$-algebra map $\iota : T \to \overline{\mathbb{Q}}$ and every $R$-algebra map $\varphi : H \to T$, the map $\varphi$ factors as $\varphi' \circ \pi$ for some $R$-algebra map $\varphi' : H' \to T$ if and only if $\iota \circ \varphi$ lies in $\Gamma$.
--
--   In scheme-theoretic language this produces the schematic closure of a Galois-stable subgroup $\Gamma$ of the $\overline{\mathbb{Q}}$-points of the finite flat commutative group scheme $\operatorname{Spec} H$ over $R$, as a finite flat closed subgroup scheme whose points in any subring of $\overline{\mathbb{Q}}$ are exactly those points of $\operatorname{Spec} H$ whose geometric point lies in $\Gamma$; it is the case $F = \mathbb{Q}$, $L = \overline{\mathbb{Q}}$ of the general statement over a principal ideal domain. It is used to construct finite flat models of Galois-stable subgroups arising from Galois representations and from Hecke torsion on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (Γ : Submonoid (WithConv (H →ₐ[R] AlgebraicClosure ℚ)))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ν : WithConv (H →ₐ[R] AlgebraicClosure ℚ)), ν ∈ Γ →
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars R).comp
        (WithConv.ofConv ν)) ∈ Γ) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H') (π : H →ₐc[R] H'),
      Function.Surjective π ∧ Module.Finite R H' ∧ Module.Flat R H' ∧
      Coalgebra.IsCocomm R H' ∧
      (RingHom.ker π = ⨅ ν ∈ Γ, RingHom.ker (WithConv.ofConv ν)) ∧
      ∀ (T : Type) [CommRing T] [Algebra R T] (ι : T →ₐ[R] AlgebraicClosure ℚ),
        Function.Injective ι →
        ∀ φ : H →ₐ[R] T,
          (∃ φ' : H' →ₐ[R] T, φ'.comp (π : H →ₐ[R] H') = φ) ↔
            WithConv.toConv (ι.comp φ) ∈ Γ := by sorry
