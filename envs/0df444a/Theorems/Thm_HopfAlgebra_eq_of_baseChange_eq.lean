-- Prove2me | Theorems.Thm_HopfAlgebra_eq_of_baseChange_eq
-- name    : HopfAlgebra.eq_of_baseChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/32587352-4199-54c8-a88b-f9ed073d376f
-- title:
--   Bialgebra maps into a flat algebra are determined generically
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and let $K$ be a field that is an $R$-algebra and a fraction field of $R$ (i.e. the structure map realises $K$ as the localisation of $R$ at its nonzero elements). Let $H$ and $H'$ be commutative rings carrying Hopf algebra structures over $R$, and assume $H'$ is flat as an $R$-module. Let $\varphi, \psi \colon H \to H'$ be two $R$-bialgebra homomorphisms, and suppose that the $K$-linear base changes of their underlying $R$-linear maps agree, that is, the two induced maps $K \otimes_R H \to K \otimes_R H'$ obtained from $\varphi$ and $\psi$ by tensoring with $K$ coincide. Then $\varphi = \psi$. Note that the hypothesis compares only the base-changed $R$-linear maps (forgetting the algebra and coalgebra structures), while the conclusion is equality in the type of $R$-bialgebra homomorphisms.
--
--   This is the faithfulness half of the statement that a morphism between flat $R$-schemes (here: affine, given by Hopf algebras) is determined by its generic fibre; it is elementary and carries no ramification or rank hypothesis, in contrast to the full-faithfulness results for finite flat group schemes. It is used in the construction of a bialgebra map with prescribed generic fibre, [`HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one`](thm.html#HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one), where it supplies the uniqueness clause.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_eq_of_baseChange_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.eq_of_baseChange_eq
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ ψ : H →ₐc[R] H')
    (h : (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : H →ₐ[R] H').toLinearMap.baseChange K) :
    φ = ψ := by sorry
