-- Prove2me | Theorems.Thm_ModularForm_logEta_add_intCast
-- name    : ModularForm.logEta_add_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/c2924f7a-2660-5811-bb1c-a08f15dfe77c
-- title:
--   Integer translation law for the logarithm of η
-- statement:
--   For every complex number $z$ and every integer $m$,
--   $$\frac{\pi i (z+m)}{12} + \sum_{n=0}^{\infty} \log\bigl(1 - q_n(z+m)\bigr) \;=\; \left(\frac{\pi i z}{12} + \sum_{n=0}^{\infty} \log\bigl(1 - q_n(z)\bigr)\right) + \frac{\pi i m}{12},$$
--   where $q_n(w) = e^{2\pi i (n+1) w}$ is Mathlib's `ModularForm.eta_q`, $\log$ is the principal branch of the complex logarithm applied termwise, and the sums are unconditional sums (`tsum`) over $n \in \mathbb{N}$, so that each side is interpreted as the value of the corresponding `tsum`, which is $0$ by convention when the family fails to be summable. The displayed expressions are the linear term plus the logarithmic series that constitute the canonical logarithm of the Dedekind $\eta$-function; the identity is stated for arbitrary $z \in \mathbb{C}$, with no hypothesis that $z$ lie in the upper half-plane and no summability hypothesis, and the integer $m$ is coerced into $\mathbb{C}$ in both occurrences.
--
--   This is the elementary translation law $\log\eta(z+m) = \log\eta(z) + \pi i m/12$ for the branch of $\log \eta$ given by the $q$-product expansion, the $T$-part of the transformation behaviour of $\eta$ under $\mathrm{SL}_2(\mathbb{Z})$. It feeds the general transformation law of this logarithm under $\mathrm{SL}_2(\mathbb{Z})$ ([`ModularForm.logEta_specialLinearGroup_smul`](thm.html#ModularForm.logEta_specialLinearGroup_smul)) and, through it, the construction of continuous roots of functions attached to principal cuspidal divisors on modular curves ([`ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor`](thm.html#ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_logEta_add_intCast.lean

import Mathlib.NumberTheory.ModularForms.DedekindEta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.logEta_add_intCast (z : ℂ) (m : ℤ) : (Real.pi * Complex.I * (z + m) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z + m))) = (Real.pi * Complex.I * z / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n z)) + Real.pi * Complex.I * m / 12 := by sorry
