-- Prove2me | Theorems.Thm_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv
-- name    : HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/c751f048-45c9-52d8-85f0-4bdac4fc7abf
-- title:
--   Cocommutativity from an abelian convolution group of Ω-points
-- statement:
--   Let $R$ be a commutative ring and $\Omega$ an algebraically closed field equipped with an $R$-algebra structure whose structure map $R \to \Omega$ is injective. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ which is flat as an $R$-module, and assume that the base change $\Omega \otimes_R H$ is a finite $\Omega$-module and is reduced. Assume further that there exist an additive commutative group $N$ and a bijection $e$ from `WithConv (H →ₐ[R] Ω)`, that is, from the set of $R$-algebra maps $H \to \Omega$ regarded as a monoid under the convolution product $f * g = m_\Omega \circ (f \otimes g) \circ \Delta$, onto $N$, such that $e(f*g) = e(f) + e(g)$ for all $f, g$. The conclusion is `Coalgebra.IsCocomm R H`: the comultiplication of $H$ followed by the flip of $H \otimes_R H$ agrees with the comultiplication, i.e. $H$ is cocommutative. Note that $e$ is only assumed to be a bijection of underlying types compatible with the two operations, no further structure being imposed on $N$ beyond that of an additive commutative group.
--
--   This is the Hopf-algebraic form of the statement that an affine group scheme which is flat and, after passing to an algebraically closed field, finite and reduced, is commutative as soon as its group of $\Omega$-points is abelian. It is used in the project to obtain cocommutativity of the Hopf algebras attached to certain finite flat group schemes, feeding the classification of such schemes by group algebras and the construction of models of torsion on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv
    (R : Type*) [CommRing R] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)]
    {N : Type*} [AddCommGroup N] (e : WithConv (H →ₐ[R] Ω) ≃ N)
    (he : ∀ f g : WithConv (H →ₐ[R] Ω), e (f * g) = e f + e g) :
    Coalgebra.IsCocomm R H := by sorry
