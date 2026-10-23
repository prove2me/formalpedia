-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_theorem_9_b
-- name    : LargeCongestion.Poisson.theorem_9_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:31.480812+00:00
-- url     : https://prove2.me/theorems/76aa43fa-0fef-45b5-acf6-711e643013c3
-- title:
--   Theorem 9(b), p. 39 — if E[|Δ²h(X)|] ≤ ν < ∞, then |E[h(S)] − E[h(X)]| ≤ (νx/2) · p e^p/(1 − p)²
-- statement:
--   Let $n \ge 1$, $S = X_1 + \dots + X_n$ with independent $X_i \sim \mathrm{Bernoulli}(p_i)$, $p_i \in (0,1)$, $x = p_1 + \dots + p_n$, $p = \max_i p_i$ and $X \sim \mathrm{Poisson}(x)$. If $h : \mathbb N \to \mathbb R$ satisfies $\mathsf E[|\Delta^2 h(X)|] \le \nu < \infty$, then $\mathsf E[h(X)]$ is finite and
--   $$\bigl|\mathsf E[h(S)] - \mathsf E[h(X)]\bigr| \le \frac{\nu x}{2}\,\frac{p\,e^{p}}{(1-p)^2} .$$
--
--   This is the Borisov–Ruzankin bound for expectations of unbounded functions; it compares a player's expected cost in a Bernoulli game with the auxiliary cost of the Poisson limit.
--
--   **Formalization Note** The hypothesis is a convergent series bounded by $\nu$. The conclusion includes summability of $k \mapsto h(k)\mathsf P(X = k)$, so that $\mathsf E[h(X)]$ is a genuine series and not Lean's default value; this follows from the hypothesis and is part of what the page asserts by writing $\mathsf E[h(X)]$. $p < 1$ comes from $p_i \in (0,1)$ and keeps $(1-p)^{-2}$ finite.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 39, Appendix C, Theorem 9(b)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Theorem 9(b), Appendix C, p. 39 (Borisov–Ruzankin): with `S`, `p_i ∈ (0, 1)`, `x = ∑ p_i`,
`p = max p_i` and `X ∼ Poisson(x)` as in Theorem 9(a), if `E[|Δ²h(X)|] ≤ ν < ∞` then
`|E[h(S)] − E[h(X)]| ≤ (ν x / 2) · p e^p / (1 − p)²`. The first conjunct records that `E[h(X)]`
is a convergent series. -/
theorem theorem_9_b {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (h : ℕ → ℝ) (ν : ℝ)
    (hint : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf (∑ i, p i) k))
    (hν : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf (∑ i, p i) k ≤ ν) :
    Summable (fun k : ℕ => h k * poissonPmf (∑ i, p i) k) ∧
      |bernoulliSumMean p h - poissonMean h (∑ i, p i)| ≤
        ν * (∑ i, p i) / 2 * ((⨆ i, p i) * Real.exp (⨆ i, p i) / (1 - ⨆ i, p i) ^ 2) := by sorry

end LargeCongestion.Poisson
