-- Prove2me | Theorems.Thm_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
-- name    : ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/425f2c08-67d0-5658-ad29-6e759a12fd2e
-- title:
--   Hasse-radicand identity in the function field of X₁(M)_κ
-- statement:
--   Let $p\ge 5$ be a prime and $\kappa$ an algebraically closed field of characteristic $p$; let $M\ge 4$ with $p\nmid M$. Let $w$ consist of a weight-one modular form on $\Gamma_1(M)$ together with an integral power series $w.\mathrm{series}$ whose image over $\mathbb{C}$ is that form's $q$-expansion and whose reduction $\mathrm{intSeriesC}\,\kappa\,w.\mathrm{series}$ (the coefficientwise image in $\kappa$, viewed as a Laurent series) is non-zero. Let $m,e_4,e_6\in\mathbb{N}$ and $S\in\kappa[X]$ satisfy: $12m+4e_4+6e_6=p-1$, $e_4\le 1$, $e_6\le 1$, $S$ monic and separable of degree $m$ with $S(0)\neq 0$ and $S(1728)\neq 0$, and, writing $\bar\jmath=\mathrm{jqModC}\,\kappa = q^{-1}\cdot\mathrm{jNum}$ for the reduced $j$-expansion and $\theta = q\,\mathrm{d}/\mathrm{d}q$ on Laurent series, $(\theta\bar\jmath)^{(p-1)/2}\,S(\bar\jmath) = (-1)^{(p-1)/2}\,\bar\jmath^{\,4m+e_4+2e_6}(\bar\jmath-1728)^{3m+e_4+e_6}$. Let $J,b,T$ lie in the intermediate field $\mathrm{x1FunctionFieldC}\,\kappa\,M\subseteq\kappa((q))$ generated over $\kappa$ by the reduced ratios of integral $q$-expansions for $\Gamma_1(M)$, with Laurent expansions $J=\bar\jmath$, $b=(\mathrm{intSeriesC}\,\kappa\,w.\mathrm{series})^{-(p-1)}$ and $T=\mathrm{intSeriesC}\,\kappa\,(w.\mathrm{series}^{12})/\mathrm{intSeriesC}\,\kappa\,(X\cdot\eta^{24})$, where $\eta^{24}=\prod_{n\ge 1}(1-X^{n})^{24}$. Then, in that field, $b^{12}\,T^{\,p-1} = J^{4e_4}(J-1728)^{6e_6}\,S(J)^{12}$.
--
--   This is the Deuring–Igusa factorisation of the Hasse invariant, transported from an identity of $q$-expansions to an identity between elements of the function field of $X_1(M)$ over $\kappa$: it is the reduction modulo $p$ of $E_{p-1}^{12}/\Delta^{p-1} = j^{4e_4}(j-1728)^{6e_6}S(j)^{12}$, with $b$ and $T$ built from the weight-one form $w$ and the discriminant series. Taking orders at a place where $J$, $J-1728$ or $S(J)$ vanishes, it feeds the computations of [`ModularCurve.ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet`](thm.html#ModularCurve.ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet) and [`ModularCurve.sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero`](thm.html#ModularCurve.sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial
open ModularCurve

theorem ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (m e₄ e₆ : ℕ) (S : Polynomial κ)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL κ (jqModC κ) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC κ) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC κ ^ (4 * m + e₄ + 2 * e₆) * (jqModC κ - 1728) ^ (3 * m + e₄ + e₆)))
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ)
    (b : ↥(ModularCurve.x1FunctionFieldC κ M)) (hb : (b : LaurentSeries κ) = w.hasseRootFn ^ (p - 1))
    (T : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hT : (T : LaurentSeries κ) =
      intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit)) :
    b ^ 12 * T ^ (p - 1) =
      J ^ (4 * e₄) * (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) ^ (6 * e₆) * (Polynomial.aeval J S) ^ 12 := by sorry
