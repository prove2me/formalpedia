-- Prove2me | Theorems.Thm_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow
-- name    : ModularCurve.hasSum_eisensteinTwoCoeff_mul_cexp_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/cdacecaa-d248-50d9-bebb-28fa540f255e
-- title:
--   q-expansion of pE₂(pτ)-E₂(τ)
-- statement:
--   Let $p$ be a natural number, assumed nonzero, and let $\tau$ be a point of the upper half-plane. Write $q = \exp(2\pi i \tau)$. Define integers $e_p(n)$ by $e_p(0) = p - 1$ and, for $n \neq 0$, $e_p(n) = 24\,\sigma'_p(n)$, where $\sigma'_p(n) = \sum_{d \mid n,\ p \nmid d} d$ is the sum of the divisors of $n$ prime to $p$ (the sum over the divisors of $n$ not divisible by $p$); this is [`ModularCurve.eisensteinTwoCoeff p n`](def/ModularCurve_EisensteinTwoCoeff.html#L7), built from [`ModularCurve.sigmaPrimeTo p n`](def/ModularCurve_EisensteinTwoCoeff.html#L5). Let $\gamma_p$ be the real invertible $2\times 2$ matrix [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21), which for $p \neq 0$ is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$, so that $\gamma_p \cdot \tau = p\tau$ in the upper half-plane. The assertion is that the family $n \mapsto e_p(n)\, q^n$, indexed by $n \in \mathbb{N}$ and viewed in $\mathbb{C}$, is summable with sum $p\,E_2(\gamma_p \cdot \tau) - E_2(\tau)$, where $E_2$ is the weight-two Eisenstein series normalised as in Mathlib.
--
--   This is the $q$-expansion of the weight-two level-$p$ Eisenstein series $pE_2(p\tau) - E_2(\tau)$, whose coefficients are $p-1$ and the prime-to-$p$ divisor sums. It is used by [`ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff`](thm.html#ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff) to realise this coefficient sequence as the $q$-expansion of an actual modular form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_eisensteinTwoCoeff_mul_cexp_pow (p : ℕ) [NeZero p] (τ : UpperHalfPlane) : HasSum (fun n : ℕ => (ModularCurve.eisensteinTwoCoeff p n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) ((p : ℂ) * EisensteinSeries.E2 (ModularForm.heckeDiagMatrix p • τ) - EisensteinSeries.E2 τ) := by sorry
