-- Prove2me | Theorems.Thm_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker
-- name    : ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/fc7e4df7-51a9-528e-ae7f-e5240dab42c9
-- title:
--   q-expansion function field of Γ₁(M₀)∩Γ₀(q) as a Γ_H field
-- statement:
--   Let $K$ be a field and let $M_0$ and $q$ be natural numbers, both nonzero, with $\gcd(M_0,q)=1$. For a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ write $F_K(\Gamma)$ for the intermediate field `qExpFunctionFieldC K` $\Gamma$ of the Laurent series field `LaurentSeries K` over $K$, namely the subfield generated over $K$ by the set `intFormRatiosC K` $\Gamma$ of Laurent series. The theorem asserts an equality of two such intermediate fields of `LaurentSeries K`. On the left is `x1x0FunctionFieldC K M₀ q`, that is $F_K(\Gamma_1(M_0)\cap\Gamma_0(q))$, the field attached to the intersection of the congruence subgroups $\Gamma_1(M_0)$ and $\Gamma_0(q)$. On the right is `xHFunctionFieldC K (M₀ * q) H`, that is $F_K(\Gamma_H(M_0q))$, where $H$ is the kernel of the reduction homomorphism $(\mathbb{Z}/M_0q)^\times \to (\mathbb{Z}/M_0)^\times$ given by `ZMod.unitsMap` applied to the divisibility $M_0 \mid M_0 q$, and where $\Gamma_H(M_0q)$ denotes the image in $\mathrm{SL}_2(\mathbb{Z})$, under the inclusion of $\Gamma_0(M_0q)$, of the preimage of $H$ under the map `gamma0Units` $(M_0q)$ sending a matrix in $\Gamma_0(M_0q)$ to the unit given by its diagonal reduction. So the two $q$-expansion function fields coincide as subfields of $K((q))$.
--
--   This is the standard identification $\Gamma_1(M_0)\cap\Gamma_0(q) = \Gamma_H(M_0q)$ for coprime $M_0,q$ and $H$ the kernel of reduction, read off at the level of the $q$-expansion function fields of the corresponding modular curves. It allows statements formulated for $X_H$ (and, in the companion corollary in the same module, for the base change of the function field to an algebraic closure of $\mathbb{Q}$) to be instantiated at the level $\Gamma_1(M_0)\cap\Gamma_0(q)$ relevant to the degeneracy/Hecke correspondence of index $q$ on $X_1(M_0)$; it is used in the computation of the action of inertia on the degree-zero Picard group of this function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker (K : Type*) [Field K] (M₀ q : ℕ)
    [NeZero M₀] [NeZero q] (h : Nat.Coprime M₀ q) :
    ModularCurve.x1x0FunctionFieldC K M₀ q =
      ModularCurve.xHFunctionFieldC K (M₀ * q) (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by sorry
