-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
-- name    : ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/f1e6c48d-23c3-5308-90a7-b3c090c75d32
-- title:
--   Nonnegative exponent vector for level Bernoulli weight sums mod q
-- statement:
--   Let $q$ be a prime. Write $\widetilde B_q(t) = 6t^2 - 6qt + q^2$ for $t$ an integer, and for $y \in \mathbb{Z}/q$ let $\mathrm{val}(y) \in \{0,\dots,q-1\}$ denote its canonical representative. The assertion is that there exist a function $\mu : \mathbb{Z}/q \to \mathbb{N}$ and natural numbers $t, e$ such that $\mu(0) = 0$, $e > 0$, and for every $x \in \mathbb{Z}/q$ with $x \neq 0$,
--   $$\sum_{r \in \mathbb{Z}/q} \mu(r)\,\widetilde B_q\bigl(\mathrm{val}(rx)\bigr) \;=\; \bigl(e \cdot [\,x = 1 \text{ or } x = -1\,]\bigr) - t,$$
--   the sum and the equality being taken in $\mathbb{Z}$ with the natural numbers $\mu(r)$, $e$, $t$ cast into $\mathbb{Z}$. Thus the integral combination of dilates $r \mapsto \widetilde B_q(\mathrm{val}(r\,\cdot))$ with nonnegative coefficients vanishing at $r = 0$ takes the value $e - t$ at $x = \pm 1$ and the constant value $-t$ at all other nonzero $x$. No normalisation of $t$ is claimed, and nothing is asserted about the value of the sum at $x = 0$.
--
--   This is the arithmetic input needed to produce a product of Siegel units on the modular curve of level $q$ whose order at the cusps, computed by the level Bernoulli weight $\widetilde B_q = 6q^2\bar B_2(\cdot/q)$, is strictly positive at one cusp above $\infty$ and constant at the remaining ones, after twisting by a power of $j$. It is used in the construction of the unit witness in [`ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit`](thm.html#ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit), and relies on the description of the rational span of the dilates of $\widetilde B_q$ as the space of even functions on $\mathbb{Z}/q$ given by [`ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even`](thm.html#ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
    (q : ℕ) [Fact q.Prime] :
    ∃ (μ : ZMod q → ℕ) (t e : ℕ), μ 0 = 0 ∧ 0 < e ∧
      ∀ x : ZMod q, x ≠ 0 →
        ∑ r : ZMod q, (μ r : ℤ) *
            (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2) =
          (if x = 1 ∨ x = -1 then (e : ℤ) else 0) - (t : ℤ) := by sorry
