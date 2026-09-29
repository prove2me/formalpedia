-- Prove2me | Theorems.Thm_HopfOrder_integralClosure_finite_of_etale
-- name    : HopfOrder.integralClosure_finite_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/e860dbce-8962-595c-880f-9a1cb7954de4
-- title:
--   Finiteness of the integral closure in an étale algebra
-- statement:
--   Let $R$ be a Noetherian integral domain that is integrally closed in its field of fractions, and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $A$ be a commutative ring carrying both a $K$-algebra structure and an $R$-algebra structure, compatible in the sense that $R \to K \to A$ is a tower (the $R$-algebra structure on $A$ is the composite of $R \to K$ with $K \to A$), and assume that $A$ is étale as a $K$-algebra, i.e. formally étale and of finite presentation over $K$. The conclusion is that the integral closure of $R$ in $A$ — the $R$-subalgebra of elements of $A$ integral over $R$ — is a finitely generated $R$-module. The three types $R$, $K$, $A$ lie in independent universes.
--
--   This is the classical finiteness of the integral closure of a Noetherian normal domain in a finite étale algebra over its fraction field. Within this development it is the finiteness input used to show that the integral closure is the greatest order, in [`HopfOrder.exists_isGreatest`](thm.html#HopfOrder.exists_isGreatest).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_integralClosure_finite_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfOrder.integralClosure_finite_of_etale
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A] : Module.Finite R ↥(integralClosure R A) := by sorry
