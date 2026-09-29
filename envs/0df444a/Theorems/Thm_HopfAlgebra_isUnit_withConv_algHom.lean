-- Prove2me | Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
-- name    : HopfAlgebra.isUnit_withConv_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/dd145ab1-68fb-5b4a-98dd-5fb1b5d4d326
-- title:
--   Points of a commutative Hopf algebra form a group
-- statement:
--   Let $R$ be a commutative semiring, let $A$ be a commutative semiring carrying a Hopf algebra structure over $R$, and let $L$ be a commutative semiring which is an $R$-algebra. Consider the type `WithConv (A →ₐ[R] L)`, i.e. the $R$-algebra homomorphisms $A \to L$ equipped with the convolution monoid structure: the product of $\varphi$ and $\psi$ is the composite of the comultiplication $A \to A \otimes_R A$ with $\varphi \otimes \psi$ followed by multiplication $L \otimes_R L \to L$, so that in Sweedler notation $(\varphi \star \psi)(a) = \sum \varphi(a_{(1)})\,\psi(a_{(2)})$, and the unit is $a \mapsto \mathrm{algebraMap}_{R,L}(\varepsilon(a))$, where $\varepsilon$ is the counit. The assertion is that every element $\varphi$ of this monoid is a unit, that is, $\varphi$ admits a two-sided inverse for the convolution product. Equivalently, the convolution monoid of $R$-algebra maps from a commutative Hopf algebra $A$ to any commutative $R$-algebra $L$ is a group.
--
--   This is the statement that the functor of points $L \mapsto \mathrm{Hom}_{R\text{-alg}}(A, L)$ of a commutative Hopf algebra takes values in groups, i.e. that $\operatorname{Spec} A$ is a group object among affine $R$-schemes. It is used in the analysis of points of finite flat group schemes occurring in the deformation-theoretic part of the argument, notably in statements about complete sets of orthogonal idempotents and about algebra maps into valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isUnit_withConv_algHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isUnit_withConv_algHom
    {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]
    {L : Type*} [CommSemiring L] [Algebra R L]
    (φ : WithConv (A →ₐ[R] L)) : IsUnit φ := by sorry
