-- Prove2me | Theorems.Thm_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one
-- name    : HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c6ca24e1-2dc0-57b2-9ed7-f8b3d8c8f480
-- title:
--   Surjectivity of Hopf algebra maps surjective on the generic fibre
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with fraction field $K$ (a field equipped with an $R$-algebra structure making it the fraction ring of $R$), and let $p$ be a prime number with $p \neq 2$ such that the image of $p$ in $R$ is irreducible, i.e. $p$ is a uniformiser of $R$. Let $H$ and $H'$ be commutative rings carrying Hopf $R$-algebra structures, each finite and flat as an $R$-module and cocommutative as an $R$-coalgebra. Let $n$ be a natural number, and assume that for every commutative $R$-algebra $T$ every $R$-algebra homomorphism $H \to T$ satisfies $f^{p^n} = 1$ in the convolution monoid structure on $\operatorname{Hom}_{R\text{-alg}}(H, T)$ recorded by `WithConv` (so the associated group of $T$-points is killed by $p^n$), and likewise for $H'$. Let $\varphi \colon H \to H'$ be a homomorphism of bialgebras over $R$ (an algebra map which is simultaneously a coalgebra map) whose base change along $R \to K$, as an $R$-linear map, is surjective $K \otimes_R H \to K \otimes_R H'$. Then $\varphi$ itself is surjective.
--
--   In the language of finite flat commutative group schemes over $R$, this is the statement that a homomorphism of finite flat commutative $p^n$-torsion group schemes over a discrete valuation ring of absolute ramification index $1$, with $p$ odd, which is a closed immersion on the generic fibre is already a closed immersion — a case of Raynaud's results on $p$-power-torsion group schemes in the range $e < p-1$. It is used in the construction of finite flat models with prescribed torsion and Hecke structure for modular curves at $j = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one
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
    (φ : H →ₐc[R] H') (hφK : Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Surjective φ := by sorry
