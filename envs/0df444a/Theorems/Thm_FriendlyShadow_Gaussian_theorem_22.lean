-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_theorem_22
-- name    : FriendlyShadow.Gaussian.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:03.954848+00:00
-- url     : https://prove2.me/theorems/b53119b3-3472-4d6f-b082-58784d21f716
-- title:
--   Theorem 22, p. 22 — parametrized shadow bound: E|edges(conv(a₁,…,aₙ) ∩ W)| ≤ 2 + 8πe² d^1.5 (L/τ)(1 + R_{n,d})(1 + 4rₙ)
-- statement:
--   Let $n\ge d\ge3$ and let $a_1,\dots,a_n\in\mathbb R^d$ be independent, $a_i$ with probability density $\mu_i$ and mean $\bar a_i$, $\|\bar a_i\|\le1$. Suppose every $\mu_i$ is $L$-log-Lipschitz, has line variance at least $\tau^2$, cutoff radius $R_{n,d}=R(1/(d\binom nd))$ at most $R$, and $n$-th deviation at most $r$, where $L,\tau>0$ and $R,r\ge0$. Then for every fixed plane $W\subseteq\mathbb R^d$, the number of edges of $\operatorname{conv}(a_1,\dots,a_n)\cap W$ is a.e. measurable and
--   $$\mathbb E\big[|\operatorname{edges}(\operatorname{conv}(a_1,\dots,a_n)\cap W)|\big]\ \le\ 2+8\pi e^2\,d^{1.5}\,\frac L\tau\,(1+R)(1+4r) .$$
--
--   This is the paper's abstract shadow bound. The paper states it as $O\big((d^{1.5}L/\tau)(1+R_{n,d})(1+r_n)\big)$; the explicit constant comes from its proof, which takes the ratio of the perimeter bound (17), $2\pi(1+4r_n)$, and the edge-length bound (18), $\tfrac12\cdot\frac{e^{-2}}{dL(1+R_{n,d})}\cdot\frac{\tau}{2\sqrt d}$, and adds the $2$ of Lemma 25. Theorems 13 and 14 follow by bounding the parameters of the Laplace–Gaussian and Laplace distributions.
--
--   **Formalization Note** The rows need not be identically distributed. The parameter predicates are upper bounds (lower bound for the line variance), which is how the page uses them ("cutoff radii at most $R_{n,d}$", "$n$-th deviations at most $r_n$"). The page's $O(\cdot)$ has $(1+r_n)$ where its proof gives $(1+4r_n)$; the proof's explicit form is kept. Positivity of $L$ and $\tau$ is implicit in the ratio $L/\tau$. The expectation is a lower Lebesgue integral, together with a.e. measurability of the edge count.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Theorem 22, p. 22; constant from the proof of Theorem 22, (17)–(18), p. 32, and Lemma 25, p. 22

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Theorem 22 (Parametrized Shadow Bound, p. 22), with the constant of its proof (p. 32):
`E|edges(conv(a₁, …, aₙ) ∩ W)| ≤ 2 + 8πe² d^{1.5} (L/τ) (1 + R) (1 + 4r)` for independent rows
with `L`-log-Lipschitz densities, centers of norm at most `1`, line variances at least `τ²`,
cutoff radii `R_{n,d}` at most `R` and `n`-th deviations at most `r`. -/
theorem theorem_22 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (L τ R r : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hr : 0 ≤ r) (hLL : ∀ i, LogLipschitz (μ i) L) (hLV : ∀ i, LineVarianceGE (μ i) τ)
    (hCR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (hND : ∀ i, NthDeviationLE (μ i) (abar i) n r) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞)) (rowLaw μ) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      ENNReal.ofReal (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) * (L / τ) *
        (1 + R) * (1 + 4 * r)) := by sorry

end FriendlyShadow.Gaussian
