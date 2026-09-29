-- Prove2me | Theorems.Thm_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one
-- name    : HopfAlgebra.bijective_of_bijective_baseChange_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/a64c53f3-7cc7-5b15-912e-22bca9cecee5
-- title:
--   Generic-fibre bijectivity descends for p-power-torsion Hopf algebras
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $p$ be a prime with $p \neq 2$ such that the image of $p$ in $R$ is irreducible, i.e. a uniformiser. Let $H$ and $H'$ be commutative rings carrying Hopf $R$-algebra structures whose comultiplications are cocommutative and which are finite and flat as $R$-modules, and let $n$ be a natural number. Assume that for every commutative $R$-algebra $T$ (in the same universe as $H$ and $H'$) and every $R$-algebra homomorphism $f \colon H \to T$, the element $f$ of the convolution monoid `WithConv (H →ₐ[R] T)` satisfies $f^{p^n} = 1$, and likewise for every $R$-algebra homomorphism $H' \to T$; thus the associated affine group schemes are killed by $p^n$ on points. Let $\varphi \colon H \to H'$ be a morphism of $R$-bialgebras, and suppose that the $K$-linear base change $K \otimes_R \varphi$ of the underlying $R$-linear map is bijective. Then $\varphi$ itself is bijective.
--
--   This is the statement, in terms of coordinate Hopf algebras, that over an absolutely unramified discrete valuation ring of odd residue characteristic (so $e = 1 < p-1$) a homomorphism of finite flat commutative $p$-power-torsion group schemes which is an isomorphism on the generic fibre is already an isomorphism, a form of Raynaud's results on prolongations of such group schemes. It is used in the proof of [`HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one`](thm.html#HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one), and is obtained here from the corresponding statement for simple quotients together with the dévissage lemma [`HopfAlgebra.surjective_of_bijective_of_bijOn_hopfKer`](thm.html#HopfAlgebra.surjective_of_bijective_of_bijOn_hopfKer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.bijective_of_bijective_baseChange_of_pow_eq_one
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
    (φ : H →ₐc[R] H') (hφK : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Bijective φ := by sorry
