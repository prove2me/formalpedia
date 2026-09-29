-- Prove2me | Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
-- name    : HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/2c9eeb31-2eb3-5c72-8ecf-37a873319f7f
-- title:
--   Unique extension of generic-fibre Hopf morphisms over a uniformising p
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with $K$ a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $p$ be a prime with $p \neq 2$ whose image in $R$ is irreducible, i.e. a uniformiser, so that the absolute ramification index is $1$. Let $H$ and $H'$ be commutative rings carrying Hopf algebra structures over $R$, each finite and flat as an $R$-module and cocommutative as an $R$-coalgebra. Let $n$ be a natural number, and assume that for every commutative $R$-algebra $T$ (in the same universe as $H$, $H'$) every element of the convolution monoid `WithConv (H →ₐ[R] T)` of $R$-algebra maps $H \to T$ satisfies $f^{p^n} = 1$, and likewise for $H'$; thus the groups of $T$-points of both schemes are killed by $p^n$. Let $\psi$ be a $K$-bialgebra homomorphism $K \otimes_R H \to K \otimes_R H'$. Then there is exactly one $R$-bialgebra homomorphism $\varphi : H \to H'$ whose underlying $R$-linear map, base changed along $R \to K$, equals the underlying $K$-linear map of $\psi$.
--
--   This is Raynaud's full faithfulness of the generic-fibre functor on finite flat commutative group schemes of $p$-power order over a discrete valuation ring of absolute ramification index $e = 1 < p - 1$ (Corollaire 3.3.6, 1°), in Hopf-algebra form: a morphism between generic fibres descends uniquely to the integral models. It is the input to Ribet's level-lowering argument, and within the formalisation it feeds the existence and uniqueness statements for maps between models of prime-power order and the construction of base-changed $F$-vector-space structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v
open scoped TensorProduct in

theorem HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
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
    (ψ : (K ⊗[R] H) →ₐc[K] (K ⊗[R] H')) :
    ∃! φ : H →ₐc[R] H',
      (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : (K ⊗[R] H) →ₐ[K] (K ⊗[R] H')).toLinearMap := by sorry
