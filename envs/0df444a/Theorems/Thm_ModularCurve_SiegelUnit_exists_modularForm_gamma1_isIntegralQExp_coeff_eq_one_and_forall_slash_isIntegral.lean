-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
-- name    : ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/511191aa-fc13-5b02-b6c2-d357f6ba5fc7
-- title:
--   Integral q-expansion of the Siegel form u_μΔ^t on Γ₁(q)
-- statement:
--   Let $q$ be a prime, let $\mu : \mathbb{Z}/q \to \mathbb{N}$ satisfy $\mu(0)=0$, and let $t \in \mathbb{N}$ be such that for every nonzero $x \in \mathbb{Z}/q$ one has $\sum_{r \in \mathbb{Z}/q} \mu(r)\bigl(6\,v(rx)^2 - 6q\,v(rx) + q^2\bigr) + t \ge 0$, where $v(y) \in \{0,\dots,q-1\}$ denotes the canonical representative of $y$. Then there is a modular form $\vartheta$ of weight $12t$ for the subgroup $\Gamma_1(q)$ of $\mathrm{GL}_2(\mathbb{R})$ such that, first, $\vartheta(\tau) = \bigl(\prod_{r,s \in \mathbb{Z}/q} \mathrm{siegelFun}\,q\,v(r)\,v(s)\,(\tau)^{12q\mu(r)}\bigr)\cdot \Delta(\tau)^t$ for all $\tau$ in the upper half-plane, where [`ModularCurve.siegelFun`](def/ModularCurve_SiegelFunction.html#L10) $q\,r\,s\,z$ is the Siegel function $-e^{\pi i s(r-q)/q^2}\,e^{\pi i((r/q)^2-r/q+1/6)z}\,(1-e^{2\pi i (rz+s)/q})\prod_{n\ge 1}(1-e^{2\pi i n z}e^{2\pi i (rz+s)/q})(1-e^{2\pi i n z}e^{-2\pi i (rz+s)/q})$ and $\Delta$ is the discriminant form; and, second, there are a power series $p \in \mathbb{Z}[[X]]$ and $n_0 \in \mathbb{N}$ with: the coefficientwise image of $p$ in $\mathbb{C}[[X]]$ equal to the $q$-expansion of $\vartheta$ of period $1$; $n_0 = \sum_{r} \mu(r)\bigl(6\,v(r)^2 - 6q\,v(r) + q^2\bigr) + t$; all coefficients of $p$ in degrees $< n_0$ zero; the coefficient in degree $n_0$ equal to $1$; and, for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ and every $n$, the $n$-th coefficient of the period-$q$ $q$-expansion of $\vartheta \mid_{12t} \gamma$ integral over $\mathbb{Z}$.
--
--   This is the existence of the Siegel modular unit package in the style of Kubert–Lang: the form $u_\mu \Delta^t$ on $\Gamma_1(q)$ has a $q$-expansion at $\infty$ with rational integer coefficients, of exact order $n_0$ given by the Bernoulli-type sum and with leading coefficient $1$, while at every cusp its expansion has algebraic integer coefficients. It is used in the construction of integral forms at full level ([`ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit`](thm.html#ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
    (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (hμ0 : μ 0 = 0) (t : ℕ)
    (ht : ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, (μ r : ℤ) *
          (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ)) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 q : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod q, ∏ s : ZMod q,
          ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
          ModularForm.discriminant τ ^ t) ∧
      ∃ (p : PowerSeries ℤ) (n₀ : ℕ), ModularCurve.IsIntegralQExp ϑ p ∧
        (n₀ : ℤ) = (∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) ∧
        (∀ n : ℕ, n < n₀ → PowerSeries.coeff n p = 0) ∧ PowerSeries.coeff n₀ p = 1 ∧
        ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
          ((UpperHalfPlane.qExpansion (q : ℝ) ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n) := by sorry
