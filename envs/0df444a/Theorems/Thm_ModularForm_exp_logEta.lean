-- Prove2me | Theorems.Thm_ModularForm_exp_logEta
-- name    : ModularForm.exp_logEta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/3b2f94f7-ff3b-5af7-b79a-6fc5855aaa23
-- title:
--   η has a canonical logarithm on H
-- statement:
--   Let $z$ be a point of the upper half-plane $\mathbb{H}$, i.e. a complex number with positive imaginary part. The assertion is the identity $$\exp\Big(\frac{\pi i z}{12}+\sum_{n=0}^{\infty}\operatorname{Log}\big(1-q_{n}(z)\big)\Big)=\eta(z),$$ where $q_n(z)=$ `ModularForm.eta_q n z` $=e^{2\pi i(n+1)z}$, $\operatorname{Log}$ is Mathlib's principal branch of the complex logarithm (so each summand is unambiguously defined because $|q_n(z)|=e^{-2\pi(n+1)\operatorname{Im} z}<1$ puts $1-q_n(z)$ in the slit plane), the sum is the `tsum` over $n\in\mathbb{N}$ of these principal logarithms, and $\eta$ is Mathlib's Dedekind eta function `ModularForm.eta`, given by the product $e^{\pi i z/12}\prod_{n\ge 0}(1-e^{2\pi i(n+1)z})$. There are no further hypotheses: the statement is the single equation, valid for every $z\in\mathbb{H}$, exhibiting the inlined expression $\pi i z/12+\sum_n\operatorname{Log}(1-q_n(z))$ as a logarithm of $\eta(z)$; the real constant $\pi$ enters through its coercion to $\mathbb{C}$.
--
--   The expression appearing under the exponential is the classical $\log\eta$ on the upper half-plane, the branch obtained by summing principal logarithms of the factors of the eta product; in particular it records that $\eta$ is nowhere vanishing on $\mathbb{H}$ and admits a continuous (indeed holomorphic) logarithm there. It is used downstream in the treatment of modular units and cuspidal divisors on modular curves, where continuous roots and powers of eta-type functions have to be constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exp_logEta.lean

import Mathlib.NumberTheory.ModularForms.DedekindEta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.exp_logEta (z : UpperHalfPlane) : Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) = ModularForm.eta z := by sorry
