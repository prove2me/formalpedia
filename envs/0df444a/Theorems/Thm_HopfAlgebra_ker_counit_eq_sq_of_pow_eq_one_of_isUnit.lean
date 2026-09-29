-- Prove2me | Theorems.Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit
-- name    : HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/fb3d5e67-e334-5499-a9a7-09ad05cce02d
-- title:
--   Augmentation ideal is idempotent when n kills all points
-- statement:
--   Let $R$ be a commutative ring and let $H$ be a commutative ring equipped with an $R$-Hopf algebra structure, and let $n$ be a natural number whose image $(n : R)$ is a unit of $R$. Assume that for every commutative ring $T$ (in the same universe as $H$) carrying an $R$-algebra structure, and every element $f$ of `WithConv (H →ₐ[R] T)` — that is, every $R$-algebra homomorphism $H \to T$, viewed in the monoid of such homomorphisms under convolution, whose multiplication is $f \ast g = (f \otimes g) \circ \Delta$ and whose unit is $T$-valued point $\varepsilon$ composed with the structure map — one has $f^{n} = 1$, the $n$-th convolution power being the convolution unit. The conclusion is an equality of ideals of $H$: the kernel of the counit, taken as the $R$-algebra homomorphism `Bialgebra.counitAlgHom R H`, equals its own square, $I = I^{2}$ with $I = \ker \varepsilon$. In geometric language, if the affine group scheme $\operatorname{Spec} H$ is killed by $n$ on $T$-points for all such $T$ and $n$ is invertible on the base, then the augmentation ideal is idempotent. No finiteness or flatness of $H$ over $R$ is assumed.
--
--   This is the affine, Hopf-algebraic form of the statement that multiplication by $n$ acts as multiplication by $n$ on the cotangent space at the identity of a commutative group scheme, so that an $n$-torsion group scheme with $n$ invertible on the base has vanishing augmentation-ideal conormal module. It is used to prove that such a Hopf algebra is étale over the base ([`HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite`](thm.html#HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite)), and thence in the analysis of torsion in the Néron model of the modular Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2 := by sorry
