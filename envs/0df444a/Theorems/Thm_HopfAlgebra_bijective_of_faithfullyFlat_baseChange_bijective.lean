-- Prove2me | Theorems.Thm_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective
-- name    : HopfAlgebra.bijective_of_faithfullyFlat_baseChange_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/09bdff76-0664-5ae8-b935-768621945aff
-- title:
--   Faithfully flat descent of bijectivity for a bialgebra map
-- statement:
--   Let $R$ be a commutative ring and let $R'$ be a commutative $R$-algebra which is faithfully flat as an $R$-module (note that $R$ and $R'$ are taken in the same universe). Let $H$ and $H'$ be commutative rings each carrying the structure of a Hopf algebra over $R$, and let $\varphi \colon H \to H'$ be a homomorphism of $R$-bialgebras, i.e. simultaneously a homomorphism of $R$-algebras and of $R$-coalgebras. Write $\varphi$ also for the underlying $R$-algebra homomorphism and hence for the underlying $R$-linear map, and assume that its base change along $R \to R'$, the $R'$-linear map $R' \otimes_R H \to R' \otimes_R H'$ sending $r \otimes h$ to $r \otimes \varphi(h)$, is bijective. The conclusion is that $\varphi$ itself is bijective as a map of sets from $H$ to $H'$.
--
--   This is the descent step of faithfully flat descent of bijectivity, in the form needed for maps of Hopf algebras: bijectivity established after a faithfully flat base change (for instance after a finite free extension of positive rank of a base discrete valuation ring) descends to the original map. It is used in the proof of [`HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple`](thm.html#HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple), part of the analysis of finite flat group schemes underlying Raynaud's uniqueness results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.bijective_of_faithfullyFlat_baseChange_bijective
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H') (hφ : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R')) :
    Function.Bijective φ := by sorry
