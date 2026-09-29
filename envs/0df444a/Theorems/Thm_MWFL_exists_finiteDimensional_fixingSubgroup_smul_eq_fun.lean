-- Prove2me | Theorems.Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_fun
-- name    : MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_fun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/d4c4e293-3208-578f-9460-d2e4148bcc57
-- title:
--   Finite level of constants in the base-changed modular function field
-- statement:
--   Let $N$ be a nonzero natural number. Write $F_N$ for `modularFunctionFieldFull N`, the subfield of the Laurent series field $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $\mathrm{qExpand}\,\mathbb{Q}\,d\,j_q$ for the nonzero divisors $d \mid N$, and write $\bar F_N$ for `modularFunctionFieldBar N`, namely `laurentBaseChange` of $F_N$ along $\mathbb{Q} \to \bar{\mathbb{Q}}$: the intermediate field of $\bar{\mathbb{Q}}((q))/\bar{\mathbb{Q}}$ generated over $\bar{\mathbb{Q}}$ by the image of $F_N$ under the coefficientwise embedding. Let $z \in \bar F_N$. The assertion is that there exists an intermediate field $L_0$ of $\bar{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ and such that for every $\sigma$ in the fixing subgroup of $L_0$, i.e. every $\sigma \in \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ with $\sigma a = a$ for all $a \in L_0$, the semilinear automorphism `arithmeticGalois` $F_N\ \sigma$ — the pair consisting of coefficientwise application of $\sigma$ to Laurent series and of $\sigma$ itself on $\bar{\mathbb{Q}}$ — fixes $z$: $\mathrm{arithmeticGalois}\,F_N\,\sigma \bullet z = z$.
--
--   This is the statement that each element of the base change of the modular function field of level $N$ to $\bar{\mathbb{Q}}$ involves only finitely many algebraic constants, so that its stabiliser for the arithmetic Galois action is open. It is used by [`ModularCurve.JZero.exists_galoisStable_rep`](thm.html#ModularCurve.JZero.exists_galoisStable_rep) to replace an element by a Galois-stable representative defined over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_fun.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_fun (N : ℕ) [NeZero N]
    (z : modularFunctionFieldBar N) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      ∀ σ ∈ L₀.fixingSubgroup, arithmeticGalois (modularFunctionFieldFull N) σ • z = z := by sorry
