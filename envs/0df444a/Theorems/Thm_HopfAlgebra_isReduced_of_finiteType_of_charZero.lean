-- Prove2me | Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
-- name    : HopfAlgebra.isReduced_of_finiteType_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a55e6b54-6f3c-5bd0-a527-09e770ae8460
-- title:
--   Cartier's theorem: Hopf algebras of finite type in characteristic zero are reduced
-- statement:
--   Let $K$ be a field of characteristic zero, and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $K$ which is of finite type as a $K$-algebra, i.e. a finitely generated $K$-algebra. The conclusion is that $A$ is a reduced ring: its only nilpotent element is $0$. No hypothesis is imposed on $A$ beyond commutativity, the Hopf algebra structure over $K$ and the finite-type condition; in particular $A$ is not assumed to be a domain, nor finite-dimensional over $K$, and $K$ is not assumed algebraically closed. In the language of affine group schemes, this says that the affine scheme $\operatorname{Spec} A$ underlying a group scheme of finite type over a field of characteristic zero is reduced.
--
--   This is the reducedness form of Cartier's theorem, which in characteristic zero upgrades to the smoothness of affine algebraic group schemes; the hypothesis on the characteristic is essential, as $\mathbb{F}_p[x]/(x^p)$ with $x$ primitive shows. It is used downstream for étaleness of module-finite Hopf algebras in characteristic zero, for statements about algebra homomorphisms into an algebraic closure, and in the verification that a proper relative group law is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.FiniteType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isReduced_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by sorry
