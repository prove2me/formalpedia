-- Prove2me | Theorems.Thm_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
-- name    : ModularCurve.exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/a7aee194-0d89-58ac-87bf-d055159445c9
-- title:
--   Affine supersingular place where a weight-one form is non-zero
-- statement:
--   Let $p\ge 5$ be a prime, let $\kappa$ be an algebraically closed field of characteristic $p$, and let $M\ge 5$ with $p\nmid M$. Let $w$ be an `IntegralWeightOneForm` for $\kappa$ and $M$: a weight-one modular form on $\Gamma_1(M)$ together with a power series $w.\mathrm{series}\in\mathbb{Z}[[q]]$ whose image in $\mathbb{C}[[q]]$ is its $q$-expansion and whose image `intSeriesC κ w.series` in $\kappa((q))$ is non-zero. Let $m,e_4,e_6\in\mathbb{N}$ and $S\in\kappa[X]$ satisfy: $12m+4e_4+6e_6=p-1$, $e_4\le 1$, $e_6\le 1$, $S$ monic and separable of degree $m$ with $S(0)\ne 0$ and $S(1728)\ne 0$, and the identity in $\kappa((q))$
--   $$(\theta \bar\jmath)^{(p-1)/2}\, S(\bar\jmath)=(-1)^{(p-1)/2}\,\bar\jmath^{\,4m+e_4+2e_6}(\bar\jmath-1728)^{3m+e_4+e_6},$$
--   where $\bar\jmath=$ `jqModC κ` is $q^{-1}$ times the reduction of `jNum` and $\theta=q\,d/dq$ is `thetaL`. Let $J$ and $u$ lie in `x1FunctionFieldC κ M`, the subfield of $\kappa((q))$ generated over $\kappa$ by the integral form ratios for $\Gamma_1(M)$, with $J=\bar\jmath$ and $u=\bar E_4/(\overline{w.\mathrm{series}})^4$, the numerator being the reduction of $1+240\sum_{n\ge 1}\sigma_3(n)q^n$. Then there is a place $x$ of this field over $\kappa$ (a proper valuation subring containing $\kappa$ and a principal ideal ring), with normalised order function $\operatorname{ord}_x$, such that $\operatorname{ord}_x J\ge 0$, $3\operatorname{ord}_x u=\operatorname{ord}_x J$ and $\operatorname{ord}_x\bigl(J^{e_4}(J-1728)^{e_6}S(J)\bigr)\ge 1$.
--
--   In classical terms: on the curve $X_1(M)$ in characteristic $p$ there is an affine point ($\operatorname{ord}_x J\ge 0$) which is supersingular (the Deuring–Igusa factor $X^{e_4}(X-1728)^{e_6}S$ of $E_{p-1}$ vanishes at $j(x)$) and at which the given weight-one form does not vanish, the second condition expressing this through $u^3=J\bar\Delta/\overline{w.\mathrm{series}}^{12}$. It is used in the construction of the character attached to the Hasse invariant divided by the $(p-1)$-st power of a weight-one form, cited by [`ModularCurve.exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow`](thm.html#ModularCurve.exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm.lean

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

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (m e₄ e₆ : ℕ) (S : Polynomial κ)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL κ (jqModC κ) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC κ) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC κ ^ (4 * m + e₄ + 2 * e₆) * (jqModC κ - 1728) ^ (3 * m + e₄ + e₆)))
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ)
    (u : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hu : (u : LaurentSeries κ) =
      intSeriesC κ (PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ)) /
        intSeriesC κ (w.series ^ 4)) :
    ∃ x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M),
      0 ≤ x.ord J ∧ 3 * x.ord u = x.ord J ∧
      1 ≤ x.ord (Polynomial.aeval J (X ^ e₄ * (X - C (1728 : κ)) ^ e₆ * S)) := by sorry
