-- Prove2me | Theorems.Thm_ModularCurve_exists_degPts_mk_eq_mk_pushforwardAlong
-- name    : ModularCurve.exists_degPts_mk_eq_mk_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/5f901dda-4e4e-59a1-a88d-14eaa4bee083
-- title:
--   Degeneracy push-forwards J_H(M) → J_{H'}(M/p) on divisor classes
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$; write $H'$ for `infSubgroup p M H hpM`, the image of $H$ under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. Let $F =$ `xHFunctionFieldBar M H` and $F' =$ `xHFunctionFieldBar (M/p) H'` be the corresponding function fields over $\overline{\mathbb{Q}}$, each obtained by adjoining to $\overline{\mathbb{Q}}$, inside the Laurent series field $\overline{\mathbb{Q}}((q))$, the coefficientwise image of the rational $q$-expansion function field of the relevant level. Let $\alpha_H, \beta_H : F' \to F$ be two $\overline{\mathbb{Q}}$-algebra homomorphisms whose underlying ring homomorphisms are integral. The assertion is that there exists a family $\mathrm{degPts} : \mathrm{Fin}\,2 \to (J_H(M) \to_+ J_{H'}(M/p))$ of additive group homomorphisms between the degree-zero divisor class groups $J_H(M) = \mathrm{Pic}^0(F)$ and $J_{H'}(M/p) = \mathrm{Pic}^0(F')$ — degree-zero divisors, i.e. finitely supported $\mathbb{Z}$-combinations of places lying in the kernel of the degree map, modulo the principal ones — such that for all degree-zero divisors $D_v$ on $F$ and $D_w$ on $F'$: if $D_w$ equals `Divisor.pushforwardAlong` $\alpha_H$ applied to $D_v$ (each place $w$ of $F$ contributing its inertia degree times its restriction to $F'$), then $\mathrm{degPts}\,0$ sends the class of $D_v$ to the class of $D_w$; and likewise with $\beta_H$ and $\mathrm{degPts}\,1$.
--
--   This packages the two degeneracy maps between Jacobians of modular curves of level $M$ and level $M/p$ as additive maps of degree-zero divisor class groups, pinned by their effect on divisors: classically the push-forward (norm) of divisors along a finite map of curves, which preserves degree zero and principal divisors and therefore descends to $\mathrm{Pic}^0$. It feeds the construction of the level data for the Néron-model picture of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_degPts_mk_eq_mk_pushforwardAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_degPts_mk_eq_mk_pushforwardAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral) :
    ∃ degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)),
      (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        degPts 0 (Pic0.mk Dv) = Pic0.mk Dw) ∧
      (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        degPts 1 (Pic0.mk Dv) = Pic0.mk Dw) := by sorry
