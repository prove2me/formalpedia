-- Prove2me | Theorems.Thm_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod
-- name    : ModularCurve.dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/9c0038a3-7166-5003-8356-cc930d847301
-- title:
--   Mod m Eisenstein recurrences force σ' coefficients
-- statement:
--   Let $p$ be a prime, let $m$ be a natural number, and let $af \colon \mathbb{N} \to \mathbb{Z}$ be any sequence of integers. Assume two families of congruences modulo $m$. First, for every prime $\ell \neq p$ and every $n \neq 0$, the integer $m$ divides $af(n\ell) + \varepsilon - (1+\ell)\,af(n)$, where $\varepsilon = \ell \cdot af(n/\ell)$ (with $n/\ell$ the natural-number quotient) when $\ell \mid n$ and $\varepsilon = 0$ otherwise; this is the weight-two Eisenstein relation for the Hecke operator $T_\ell$, whose eigenvalue is taken to be $1+\ell$. Second, for every $n \neq 0$, the integer $m$ divides $af(np) - af(n)$, the relation at $p$ with eigenvalue $1$. The conclusion is that for every $n \neq 0$, $m$ divides $af(n) - \sigma'_p(n)\,af(1)$, where $\sigma'_p(n)$ is `sigmaPrimeTo p n`, the sum of those divisors of $n$ that are not divisible by $p$, cast into $\mathbb{Z}$. No positivity or nontriviality hypothesis is imposed on $m$, and nothing is asserted about $af(0)$.
--
--   This is the elementary arithmetic core of the statement that a weight-two form whose Hecke eigenvalues are congruent to the Eisenstein ones modulo $m$ has, away from the constant term, the $q$-expansion of the Eisenstein series with coefficients $\sigma'_p$. It is used in the Eisenstein-ideal part of the development, by [`CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator`](thm.html#CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator) and by [`ModularCurve.exists_mem_eisensteinIdeal_heckeProj_eq_eisensteinNumerator`](thm.html#ModularCurve.exists_mem_eisensteinIdeal_heckeProj_eq_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod (p m : ℕ) [Fact p.Prime] (af : ℕ → ℤ) (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) (hU : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 := by sorry
