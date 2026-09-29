-- Prove2me | Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
-- name    : ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5d146440-ce87-500c-b526-1277a754aaf6
-- title:
--   (thetajmath̄)^{q-1} as a rational function of jmath̄
-- statement:
--   Let $q\ge 5$ be a prime, and let $m,e_4,e_6$ be natural numbers with $12m+4e_4+6e_6=q-1$, $e_4\le 2$ and $e_6\le 1$. Let $k$ be an algebraically closed field of characteristic $q$, and let $S_0$ be a finite subset of $k$ whose elements are exactly the members of `ssJSet q k`, that is, the $j\in k$ such that every elliptic Weierstrass curve $W$ over $k$ with $W.j = j$ has no nonzero point $P$ of its affine model with $q\cdot P=0$ (the supersingular $j$-invariants). Write $\bar\jmath =$ `jqModC k` for the Laurent series $\mathfrak q^{-1}\cdot (E_4^3\,\eta\text{-unit}^{-1})$ over $k$, the reduction of the $q$-expansion of the modular invariant, and let $\theta$ be the $k$-linear operator $f\mapsto \mathfrak q\,\frac{df}{d\mathfrak q}$ on $k((\mathfrak q))$. Then
--   $$(\theta\bar\jmath)^{q-1}\cdot\Big(\prod_{a\in S_0\setminus\{0,1728\}}(\bar\jmath - a)\Big)^{2} = \bar\jmath^{\,8m+2e_4+4e_6}\,(\bar\jmath-1728)^{\,6m+2e_4+2e_6},$$
--   an identity of Laurent series over $k$, the subtracted $a$ and $1728$ being constant series.
--
--   This is the mod-$q$ Kronecker-type identity expressing $(\theta\bar\jmath)^{q-1}$ as a rational function of $\bar\jmath$ whose polar divisor is supported on the supersingular $j$-invariants of width one, obtained by extracting a sixth root of the product of the supersingular factorisation of $\bar\Delta^{q-1}$ and the identity $(\theta j)^6 = j^4(j-1728)^3\Delta$. It is used in the study of the theta operator on mod-$q$ modular forms, in particular in the results on weight-one forms and on separability and valuations of $(\theta\bar\jmath)$-powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    thetaL k (jqModC k) ^ (q - 1) *
        (∏ a ∈ S₀ \ {0, 1728}, (jqModC k - HahnSeries.C a)) ^ 2 =
      jqModC k ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC k - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by sorry
