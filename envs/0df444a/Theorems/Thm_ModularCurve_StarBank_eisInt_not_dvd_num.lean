-- Prove2me | Theorems.Thm_ModularCurve_StarBank_eisInt_not_dvd_num
-- name    : ModularCurve.StarBank.eisInt_not_dvd_num
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/49c86ba7-b6c8-5534-ad98-1771659f0c35
-- title:
--   A prime ℓ ≥ 5 does not divide num(B_{ℓ-1})
-- statement:
--   Let $\ell$ be a natural number that is prime, and assume $5 \le \ell$. The assertion is that the integer $\ell$ does not divide the numerator of the rational number $B_{\ell-1}$, where `bernoulli` denotes Mathlib's Bernoulli numbers (the convention with $B_1 = 1/2$) and the numerator is the one of the canonical representation of a rational in lowest terms with positive denominator, so that $\mathrm{num}$ and $\mathrm{den}$ are coprime. The index $\ell - 1$ is truncated natural subtraction, which under the hypothesis $5 \le \ell$ is the ordinary $\ell - 1 \ge 4$; the hypothesis is what ties the index to the prime, and the statement is false for unrelated indices (for instance $691$ divides the numerator of $B_{12}$). Equivalently, $B_{\ell-1}$ is nonzero and, when written in lowest terms, has $\ell$-adic valuation exactly $-1$ for its denominator rather than any positive power of $\ell$ in its numerator.
--
--   This is the standard consequence of the von Staudt–Clausen congruence for the particular index $\ell - 1$: since $(\ell-1) \mid (\ell-1)$, the prime $\ell$ enters the denominator of $B_{\ell-1}$, and coprimality of numerator and denominator then forbids $\ell$ from dividing the numerator. It is used to see that the constant term of the integral Eisenstein series of weight $\ell - 1$ is a unit modulo $\ell$, so that its reduction modulo $\ell$ is a nonzero constant; in this form it feeds the construction [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) and the statements about $q$-expansion models of $j$ and of cusp forms that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_eisInt_not_dvd_num.lean

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ArithmeticFunction.sigma
open Finset

theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by sorry
