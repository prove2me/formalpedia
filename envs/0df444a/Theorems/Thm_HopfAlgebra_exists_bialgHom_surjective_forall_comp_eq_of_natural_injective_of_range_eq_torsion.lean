-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
-- name    : HopfAlgebra.exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/55dd7383-8231-5633-854b-42370bf713d1
-- title:
--   Natural torsion point inclusion comes from a bialgebra quotient
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and let $H$ and $H'$ be commutative Hopf algebras over $R$ (both in a single universe $v$). Suppose given, for every commutative $R$-algebra $T$ in that universe, a map $\iota_T \colon \operatorname{Hom}_{R\text{-alg}}(H,T) \to \operatorname{Hom}_{R\text{-alg}}(H',T)$ subject to four hypotheses: naturality, $\iota_{T'}(g \circ \psi) = g \circ \iota_T(\psi)$ for every $R$-algebra map $g \colon T \to T'$ and every $\psi \colon H \to T$; multiplicativity for the convolution product on points, $\iota_T(\psi_1 * \psi_2) = \iota_T(\psi_1) * \iota_T(\psi_2)$, the products being taken in the convolution monoid structure on algebra homomorphisms out of a Hopf algebra (transported along `toConv`/`ofConv`); injectivity of $\iota_T$ for every $T$; and the requirement that the image of $\iota_T$ consist exactly of the $n$-torsion, i.e. an $R$-algebra map $x \colon H' \to T$ lies in the range of $\iota_T$ if and only if its $n$-th convolution power equals the unit of the convolution monoid. The conclusion is that there exists a bialgebra homomorphism $\pi \colon H' \to H$ over $R$ which is surjective and satisfies $\iota_T(\psi) = \psi \circ \pi$ for every commutative $R$-algebra $T$ and every $\psi \colon H \to T$.
--
--   This is the Yoneda-style recognition statement that a subfunctor of points of $\operatorname{Spec} H'$ cut out by the condition of being $n$-torsion, when it is represented by a Hopf algebra $H$ compatibly with the group law, is represented by a closed subgroup scheme, i.e. the representing comparison map is a surjection of bialgebras $H' \twoheadrightarrow H$. It is used in the construction of finite flat models of torsion in Jacobians of modular curves, in [`ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL) and [`ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open WithConv

theorem HopfAlgebra.exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
    {R : Type u} [CommRing R] (n : ℕ)
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type v) [CommRing H'] [HopfAlgebra R H']
    (ι : ∀ (T : Type v) [CommRing T] [Algebra R T], (H →ₐ[R] T) → (H' →ₐ[R] T))
    (hnat : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (g : T →ₐ[R] T') (ψ : H →ₐ[R] T), ι T' (g.comp ψ) = g.comp (ι T ψ))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ₁ ψ₂ : H →ₐ[R] T),
      ι T (toConv ψ₁ * toConv ψ₂).ofConv = (toConv (ι T ψ₁) * toConv (ι T ψ₂)).ofConv)
    (hinj : ∀ (T : Type v) [CommRing T] [Algebra R T], Function.Injective (ι T))
    (htors : ∀ (T : Type v) [CommRing T] [Algebra R T] (x : H' →ₐ[R] T),
      x ∈ Set.range (ι T) ↔ toConv x ^ n = 1) :
    ∃ π : H' →ₐc[R] H, Function.Surjective π ∧
      ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ : H →ₐ[R] T), ι T ψ = ψ.comp (π : H' →ₐ[R] H) := by sorry
