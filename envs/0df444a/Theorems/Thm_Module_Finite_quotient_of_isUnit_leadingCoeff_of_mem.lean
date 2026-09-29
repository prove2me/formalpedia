-- Prove2me | Theorems.Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem
-- name    : Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/21d57877-2c48-517a-a2e1-59ea7f7f0285
-- title:
--   Finiteness over R of A/I when I contains a polynomial with unit leading coefficient
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative ring which is both an $R$-algebra and an $R[X]$-algebra, the two structures being compatible in the sense that the scalar tower condition for $R$, $R[X]$, $A$ holds, and suppose $A$ is a finite (finitely generated) module over $R[X]$. Let $N \in R[X]$ be a polynomial whose leading coefficient is a unit of $R$, and let $I$ be an ideal of $A$ containing the image $\mathrm{algebraMap}_{R[X],A}(N)$ of $N$ in $A$. Then the quotient ring $A/I$ is a finite $R$-module, that is, finitely generated as a module over $R$. Note that $N$ is not assumed monic, only that its leading coefficient is invertible, and that no Noetherian or flatness hypothesis on $R$ or $A$ is imposed.
--
--   This is the finiteness half of the standard "norm trick": a closed subscheme of a curve cut out by a function whose norm down to $R[X]$ has invertible leading coefficient is finite over the base. It is used in the construction of level rings and charts on modular curves, for instance by [`ModularCurve.HpoolLevelRing.finite_levelRing`](thm.html#ModularCurve.HpoolLevelRing.finite_levelRing) and [`ModularCurve.DRModelPackageLevel.exists_forall_finite_quotient_span_aeval_and_finrank_le`](thm.html#ModularCurve.DRModelPackageLevel.exists_forall_finite_quotient_span_aeval_and_finrank_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u v

theorem Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] [Module.Finite R[X] A]
    (N : R[X]) (hN : IsUnit N.leadingCoeff) (I : Ideal A) (hNI : algebraMap R[X] A N ∈ I) :
    Module.Finite R (A ⧸ I) := by sorry
