-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_theorem_13
-- name    : FriendlyShadow.Gaussian.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:34.670329+00:00
-- url     : https://prove2.me/theorems/30c62726-62ea-47c1-97bd-6f0d8c03e9ce
-- title:
--   Theorem 13, p. 19 — Gaussian rows: E|edges(conv(a₁,…,aₙ) ∩ W)| ≤ 3 + 128πe²d²√(log n)σ⁻²(1 + 4σ√(d log n))(1 + 16σ√(log n))
-- statement:
--   Let $W\subseteq\mathbb R^d$ be a fixed two-dimensional subspace, $n\ge d\ge3$, and let $a_1,\dots,a_n\in\mathbb R^d$ be independent Gaussian random vectors, $a_i\sim N_d(\bar a_i,\sigma)$ with standard deviation $\sigma>0$ in every coordinate and centers $\|\bar a_i\|\le1$. Then the number of edges of the shadow polygon $\operatorname{conv}(a_1,\dots,a_n)\cap W$ is a.e. measurable and
--   $$\mathbb E\big[|\operatorname{edges}(\operatorname{conv}(a_1,\dots,a_n)\cap W)|\big]\ \le\ 3+\frac{128\pi e^2\,d^2\sqrt{\log n}}{\sigma^2}\big(1+4\sigma\sqrt{d\log n}\big)\big(1+16\sigma\sqrt{\log n}\big).$$
--
--   Expanded, the right-hand side is $O\big(d^2\sqrt{\log n}\,\sigma^{-2}+d^{2.5}\log n\,\sigma^{-1}+d^{2.5}\log^{1.5}n\big)$, the paper's $\mathcal D_g(d,n,\sigma)$. By the shadow vertex method, this quantity bounds the expected number of pivot steps of a shadow path on a smoothed unit LP $\{x:Ax\le\mathbf 1\}$ with Gaussian-perturbed rows.
--
--   **Formalization Note** The paper writes the bound as $O(\cdot)$. The constant here is the one its proof yields: Lemma 46 adds $1$; Theorem 22's proof gives $2+8\pi e^2d^{1.5}(L/\tau)(1+R_{n,d})(1+4r_n)$; Lemma 45 supplies $L=4\sigma^{-1}\sqrt{d\log n}$, $\tau\ge\sigma/4$, $R_{n,d}\le4\sigma\sqrt{d\log n}$, $r_n\le4\sigma\sqrt{\log n}$. The page writes "$\mathcal D_g(n,d,\sigma)$" against its definition "$\mathcal D_g(d,n,\sigma)$", a slip in the argument order. $\sigma>0$ is implicit on the page. $\log$ is natural. $W$ is a parameter, independent of the random vectors. The expectation is a lower Lebesgue integral, together with a.e. measurability, so it is a genuine expectation.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Theorem 13, p. 19; constants from the proof of Theorem 22, (17)–(18), p. 32, Lemma 45, p. 34, Lemma 46, p. 35, and the proof of Theorem 13, p. 36

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Theorem 13 (p. 19), with the constants of its proof (Theorem 22 via (17)–(18), p. 32;
Lemma 45, p. 34; Lemma 46, p. 35). Let `W ⊂ ℝᵈ` be a fixed two-dimensional subspace,
`n ≥ d ≥ 3`, and let `a₁, …, aₙ` be independent Gaussian vectors `aᵢ ∼ N_d(āᵢ, σ)`, `σ > 0`, with
`‖āᵢ‖ ≤ 1`. Then the number of edges of `conv(a₁, …, aₙ) ∩ W` is a measurable random variable
(almost everywhere) and
`E|edges(conv(a₁, …, aₙ) ∩ W)| ≤ 3 + 128πe² d² √(log n) σ⁻² (1 + 4σ√(d log n)) (1 + 16σ√(log n))`. -/
theorem theorem_13 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (σ : ℝ) (hσ : 0 < σ) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ≤
      ENNReal.ofReal (3 + 128 * Real.pi * Real.exp 2 * (d : ℝ) ^ 2 * Real.sqrt (Real.log n) /
        σ ^ 2 * (1 + 4 * σ * Real.sqrt (d * Real.log n)) *
        (1 + 16 * σ * Real.sqrt (Real.log n))) := by sorry

end FriendlyShadow.Gaussian
