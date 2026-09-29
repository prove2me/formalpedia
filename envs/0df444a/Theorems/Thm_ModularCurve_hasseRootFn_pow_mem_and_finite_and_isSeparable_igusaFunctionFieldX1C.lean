-- Prove2me | Theorems.Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
-- name    : ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/dbf48f79-5243-5c70-8ffc-0cbc64e783cc
-- title:
--   Kummer relation, finiteness and separability of the Igusa field
-- statement:
--   Let $p$ be a prime, let $M$ be a non-zero natural number with $5 \le M$ and $p \nmid M$, let $\kappa$ be a field of characteristic $p$, and let $w$ be an integral weight-one form of level $M$ over $\kappa$, i.e. a triple consisting of a modular form `form` of weight $1$ on $\Gamma_1(M)$, a power series `series` over $\mathbb{Z}$ whose image under $\mathbb{Z} \to \mathbb{C}$ is the weight-one $q$-expansion of `form`, together with the requirement that `intSeriesC κ series`, the Laurent series over $\kappa$ obtained from the coefficientwise reduction of `series` to $\kappa$, is non-zero. Write $a =$ `w.hasseRootFn` $= ($`intSeriesC κ w.series`$)^{-1} \in \kappa((q))$, let $K_0 =$ `x1FunctionFieldC κ M` be the intermediate field of $\kappa((q)) / \kappa$ generated over $\kappa$ by the set `intFormRatiosC κ (Gamma1 M)`, and let $\mathrm{Ig} =$ `igusaFunctionFieldX1C κ M w` be the intermediate field generated over $\kappa$ by $K_0 \cup \{a\}$, regarded as an extension of $K_0$ via the inclusion $K_0 \le \mathrm{Ig}$. The assertion is threefold: $a^{p-1}$ lies in $K_0$; $\mathrm{Ig}$ is a finite $K_0$-module; and $\mathrm{Ig}$ is separable over $K_0$.
--
--   This is the basic structural statement about the Igusa cover in the $q$-expansion model: adjoining the inverse of the reduction of an integral weight-one form to the level-$M$ modular function field in characteristic $p$ gives a finite separable Kummer extension of exponent dividing $p-1$, the $q$-expansion incarnation of Igusa's model of the Igusa curve. It is used downstream in the computation of ramification indices along the inclusion of function fields and in the analysis of the local models of $X_1(M)$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] (w : ModularCurve.IntegralWeightOneForm κ M) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C κ M w)).toRingHom.toAlgebra
    w.hasseRootFn ^ (p - 1) ∈ ModularCurve.x1FunctionFieldC κ M ∧
    Module.Finite ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) ∧
    Algebra.IsSeparable ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) := by sorry
