-- Prove2me | Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
-- name    : HopfAlgebra.algebra_etale_of_module_finite_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d2831c9c-c946-5052-abd4-0f79949bd86f
-- title:
--   Finite Hopf algebras in characteristic zero are étale
-- statement:
--   Let $K$ be a field of characteristic zero and let $A$ be a commutative ring equipped with the structure of a Hopf algebra over $K$ (in particular a commutative $K$-algebra with comultiplication, counit and antipode) which is finite as a $K$-module, i.e. finitely generated as a $K$-vector space. The conclusion is `Algebra.Etale K A`: $A$ is an étale $K$-algebra, which in Mathlib's formulation means that $A$ is formally étale over $K$ (the lifting property for square-zero extensions holds with existence and uniqueness) and that $A$ is of finite presentation as a $K$-algebra. No cocommutativity of the Hopf algebra structure is assumed, and the field $K$ is not assumed algebraically closed; finiteness of $A$ as a $K$-module is the only finiteness hypothesis.
--
--   This is the zero-dimensional case of Cartier's theorem, that affine group schemes over a field of characteristic zero are smooth: the finite group scheme $\operatorname{Spec} A$ is finite étale over $K$. It is used throughout the Hopf-algebra layer of the project, for instance in computing the number of algebra homomorphisms out of a finite flat Hopf algebra in terms of its rank and in comparisons of Hopf orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Field

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.algebra_etale_of_module_finite_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by sorry
