-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_theorem_2_9
-- name    : KallMayerSLP.GenConcave.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:46.865767+00:00
-- url     : https://prove2.me/theorems/126ee184-cd90-4929-a600-cb94a54ea5b3
-- title:
--   Theorem 2.9 (Prékopa) — marginals of logconcave functions are logconcave
-- statement:
--   Let $f:\mathbb R^{n+m}\to\mathbb R_+$ be a logconcave function, that is,
--
--   $$
--   f(\lambda u+(1-\lambda)v)\ \ge\ f(u)^\lambda f(v)^{1-\lambda}\qquad\text{for all }u,v\in\mathbb R^{n+m},\ \lambda\in[0,1].
--   $$
--
--   Then the marginal
--
--   $$
--   g(x):=\int_{\mathbb R^m} f(x,y)\,dy
--   $$
--
--   is a logconcave function on $\mathbb R^n$: $g(\lambda x+(1-\lambda)x')\ge g(x)^\lambda g(x')^{1-\lambda}$ for all $x,x'\in\mathbb R^n$, $\lambda\in[0,1]$.
--
--   Consequences: all marginal densities of a logconcave density are logconcave, and the convolution of two logconcave densities is logconcave.
--
--   **Formalization Note** $\mathbb R^{n+m}$ is the product $\mathbb R^n\times\mathbb R^m$; logconcavity of $f$ is $0$-concavity (Definition 2.3). The marginal is the Lebesgue integral with values in $[0,\infty]$ and the logconcavity inequality for $g$ is read in $[0,\infty]$, so no integrability of the sections is assumed; when every section is integrable this is the statement for the real-valued $g$. No measurability of $f$ is assumed (a logconcave function is quasi-concave, hence Lebesgue measurable).
--
--   Differences from the source:
--   - generalization: $g(x)=\int f(x,y)\,dy$ a real-valued function (sections integrable) → $g$ with values in $[0,\infty]$, no integrability assumed; reason: when every section is integrable the $[0,\infty]$ inequality is the book's inequality for the real $g$
--   - encoding: $\mathbb R^{n+m}$ → $\mathbb R^n\times\mathbb R^m$; reason: Lean convention, same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.9, p.127 (PDF 137) (cited from Prékopa [227]); logconcavity, Definition 1.3, p.90 (PDF 100)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun

open MeasureTheory

namespace KallMayerSLP.GenConcave

/-- **Theorem 2.9 (Prékopa)** (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 2, Theorem 2.9, p. 127, PDF p. 137; cited from Prékopa [227]). Let
`f : ℝ^{n+m} → ℝ₊` be a logconcave function. Then `g(x) := ∫_{ℝ^m} f(x, y) dy` is a
logconcave function on `ℝⁿ`.

**Formalization Note.** `ℝ^{n+m}` is `(Fin n → ℝ) × (Fin m → ℝ)`. Logconcavity of `f` is
`0`-concavity (Definition 2.3 with `γ = 0`, which the book identifies with logconcavity on
p. 123; it is Definition 1.3, p. 90). The marginal `g` is the Lebesgue integral
`∫⁻ y, f(x, y)` with values in `[0, ∞]`, and logconcavity of `g` is the inequality
`g(λx + (1 − λ)y) ≥ g(x)^λ g(y)^{1−λ}` of Definition 1.3 read in `[0, ∞]`; no integrability
of the sections is assumed. When every section is integrable this is the book's
statement for the real-valued `g`. No measurability of `f` is assumed: a logconcave
function is quasi-concave, so its sections are Lebesgue measurable. -/
theorem theorem_2_9 {n m : ℕ} (f : (Fin n → ℝ) × (Fin m → ℝ) → ℝ)
    (hf : IsGammaConcaveFun 0 f) :
    ∀ x y : Fin n → ℝ, ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      (∫⁻ z, ENNReal.ofReal (f (x, z))) ^ lam * (∫⁻ z, ENNReal.ofReal (f (y, z))) ^ (1 - lam) ≤
        ∫⁻ z, ENNReal.ofReal (f (lam • x + (1 - lam) • y, z)) := by sorry

end KallMayerSLP.GenConcave
