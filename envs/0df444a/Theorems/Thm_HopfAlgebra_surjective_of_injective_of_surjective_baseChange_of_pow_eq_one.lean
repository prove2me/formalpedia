-- Prove2me | Theorems.Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one
-- name    : HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c87dd7c9-b442-5585-9832-8aa9d80d4efb
-- title:
--   Injective bialgebra maps of p-power-order Hopf algebras, surjective generically
-- statement:
--   Let $R$ be a discrete valuation ring which is a commutative domain, with fraction field $K$ (a field with an $R$-algebra structure making it the fraction field of $R$, in the same universe as $R$), let $p$ be a prime, assume $p \neq 2$ and that $p$, viewed in $R$, is irreducible, i.e. a uniformiser. Let $H$ and $H'$ be commutative rings in a universe $v$, each carrying a Hopf algebra structure over $R$ whose underlying coalgebra is cocommutative and whose underlying $R$-module is finite and flat. Fix $n \in \mathbb{N}$ and assume that for every commutative $R$-algebra $T$ in the universe $v$, every element of the convolution monoid `WithConv` on $R$-algebra homomorphisms $H \to T$ satisfies $f^{p^n} = 1$, and likewise for $H'$; that is, both group schemes are killed by $p^n$. Let $j : H \to H'$ be a bialgebra homomorphism over $R$ which is injective as a function, and assume that the base change of its underlying $R$-linear map along $K$, namely $K \otimes_R j : K \otimes_R H \to K \otimes_R H'$, is surjective. The conclusion is that $j$ itself is surjective.
--
--   This is the surjectivity half of Raynaud's theorem that, for absolute ramification index $e = 1 < p-1$, a morphism of finite flat commutative $p$-power-order group schemes over $R$ which is an isomorphism on generic fibres is an isomorphism; in the group-scheme language, two prolongations of the same finite $K$-group, one dominating the other, coincide. It feeds the full faithfulness of the generic-fibre functor used in the local analysis of prolongations, being cited by [`HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one`](thm.html#HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one) and [`HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one`](thm.html#HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (j : H →ₐc[R] H') (hj : Function.Injective j)
    (hjK : Function.Surjective ((j : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Surjective j := by sorry
