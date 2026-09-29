-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
-- name    : ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/3275d8db-a9a3-5069-aeb0-a652b3b217bb
-- title:
--   Supersingular j-invariants are the roots of X^{e₄}(X-1728)^{e₆}S
-- statement:
--   Let $p$ be a prime with $5 \le p$ and let $\Omega$ be an algebraically closed field of characteristic $p$. Let $m, e_4, e_6$ be natural numbers and $S \in \Omega[X]$, subject to the following single conjunction of hypotheses: $12m + 4e_4 + 6e_6 = p - 1$; $e_4 \le 1$; $e_6 \le 1$; $S$ is monic; $S$ is separable; $S$ has natural degree $m$; $S(0) \ne 0$; $S(1728) \ne 0$; and, writing $\bar\jmath =$ `jqModC` $\Omega$ for the Laurent series $q^{-1}\cdot E_4^3\eta^{-24}$ over $\Omega$ (the image of the integral power series `jNum` $=$ `eisenstein4`$^3\cdot$`dedekindEtaUnitInv` shifted by $q^{-1}$) and $\theta$ for the $\Omega$-linear operator $f \mapsto q\, f'$ on $\Omega((q))$, the identity $$(\theta\bar\jmath)^{(p-1)/2}\cdot S(\bar\jmath) = (-1)^{(p-1)/2}\left(\bar\jmath^{\,4m+e_4+2e_6}(\bar\jmath-1728)^{3m+e_4+e_6}\right)$$ holds in $\Omega((q))$, where $S(\bar\jmath)$ means the evaluation of $S$ at $\bar\jmath$ under the $\Omega$-algebra structure. Then for every $j_0 \in \Omega$: $j_0$ lies in `ssJSet` $p\,\Omega$, that is, every elliptic Weierstrass curve $W$ over $\Omega$ with $j$-invariant $j_0$ has trivial $p$-torsion in its group of affine points, if and only if $X^{e_4}(X - 1728)^{e_6}S$ vanishes at $j_0$.
--
--   This is Deuring's description of the supersingular locus in characteristic $p \ge 5$: the supersingular $j$-invariants are exactly the roots of the Deuring–Igusa polynomial $X^{e_4}(X-1728)^{e_6}S(X)$ attached to the data $(m,e_4,e_6,S)$, with $e_4 = 1$ precisely when $p \equiv 2 \pmod 3$ and $e_6 = 1$ precisely when $p \equiv 3 \pmod 4$. It is used downstream in the ramification and degree computations on $X_0$ and $X_1$ level structures, where supersingular points must be recognised as zeros of an explicit polynomial in $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open ModularCurve

theorem ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (m e₄ e₆ : ℕ) (S : Polynomial Ω)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL Ω (jqModC Ω) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC Ω) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC Ω ^ (4 * m + e₄ + 2 * e₆) * (jqModC Ω - 1728) ^ (3 * m + e₄ + e₆)))
    (j₀ : Ω) :
    j₀ ∈ ModularCurve.ssJSet p Ω ↔ Polynomial.eval j₀ (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * S) = 0 := by sorry
