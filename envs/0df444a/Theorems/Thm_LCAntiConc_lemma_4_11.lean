-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_11
-- name    : LCAntiConc.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:24.620421+00:00
-- url     : https://prove2.me/theorems/39e58224-b9c6-42b9-bb52-0d4c502a40be
-- title:
--   Lemma 4.11 — univariate majorant of the box indicator for Laplace and Gaussian weights
-- statement:
--   There are universal constants $C,\delta_0>0$ such that for every $0<a\le1$, every $0<\delta<\delta_0$, and each of the weights $w(t)=e^{-a|t|}$ and $w(t)=e^{-at^2}$, there is an even polynomial $q$ which is the square of an even polynomial and satisfies
--
--   $$q(t)\ge0\ (t\in\mathbb R),\qquad q(t)\ge1\ (|t|\le\delta),\tag{4.22}$$
--
--   $$\int_{\mathbb R}q(t)w(t)\,dt\le C\delta,\qquad |q^{(r)}(t)|\le C\,\delta^{-r}w(t)^{-1}\quad(t\in\mathbb R,\ r\in\{0,1,2\}).\tag{4.23}$$
--
--   Its degree is $m\le\exp(C/(a\delta))$ for the Laplace weight and $m\le C/(a\delta^2)$ for the Gaussian weight.
--
--   These majorants are the polynomials $q$ of Theorems 4.9 and 4.10.
--
--   Differences from the source:
--   - reading: each O(·) (in ∫qw, in the derivative bounds, and the degree bounds' C) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.11, (4.22)–(4.23), p.28 (PDF p.30); restated p.47 (PDF p.49)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.11** (Univariate majorant). There are universal constants `C, δ₀ > 0` such that for
every `0 < a ≤ 1`, `0 < δ < δ₀`, and each of the weights `w(t) = e^{-a|t|}` and `w(t) = e^{-at²}`,
there is an even polynomial `q` which is the square of an even polynomial and satisfies
`q(t) ≥ 0` (`t ∈ ℝ`), `q(t) ≥ 1` (`|t| ≤ δ`) (4.22), `∫_ℝ q w ≤ O(δ)` and
`|q^{(r)}(t)| ≤ O(δ^{-r} w(t)^{-1})` (`t ∈ ℝ`, `r ∈ {0, 1, 2}`) (4.23). Its degree is
`m ≤ exp(C/(aδ))` for the Laplace weight and `m ≤ C/(aδ²)` for the Gaussian weight.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.11, p.28 (PDF p.30); restated p.47 (PDF p.49).

**Formalization Note** One universal constant `C` serves every `O(·)` and both degree bounds; it
and `δ₀` come before `a` and `δ`. The two weights give the two conjuncts. -/
theorem lemma_4_11 :
    ∃ C > 0, ∃ δ₀ > 0, ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (∃ q : Polynomial ℝ,
        (∃ p : Polynomial ℝ, (∀ t, p.eval (-t) = p.eval t) ∧ q = p ^ 2) ∧
        (∀ t, q.eval (-t) = q.eval t) ∧ (∀ t, 0 ≤ q.eval t) ∧ (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧
        ∫ t, q.eval t * Real.exp (-a * |t|) ≤ C * δ ∧
        (∀ r : ℕ, r ≤ 2 → ∀ t, |((⇑Polynomial.derivative)^[r] q).eval t| ≤
          C * δ ^ (-(r : ℤ)) * (Real.exp (-a * |t|))⁻¹) ∧
        (q.natDegree : ℝ) ≤ Real.exp (C / (a * δ))) ∧
      (∃ q : Polynomial ℝ,
        (∃ p : Polynomial ℝ, (∀ t, p.eval (-t) = p.eval t) ∧ q = p ^ 2) ∧
        (∀ t, q.eval (-t) = q.eval t) ∧ (∀ t, 0 ≤ q.eval t) ∧ (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧
        ∫ t, q.eval t * Real.exp (-a * t ^ 2) ≤ C * δ ∧
        (∀ r : ℕ, r ≤ 2 → ∀ t, |((⇑Polynomial.derivative)^[r] q).eval t| ≤
          C * δ ^ (-(r : ℤ)) * (Real.exp (-a * t ^ 2))⁻¹) ∧
        (q.natDegree : ℝ) ≤ C / (a * δ ^ 2)) := by sorry

end LCAntiConc
