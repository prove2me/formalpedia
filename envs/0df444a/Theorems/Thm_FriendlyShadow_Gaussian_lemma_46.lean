-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_46
-- name    : FriendlyShadow.Gaussian.lemma_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:19.965542+00:00
-- url     : https://prove2.me/theorems/c5747d22-bf30-4e9c-bea5-0a9567f30b1c
-- title:
--   Lemma 46, p. 35 — E_{N_d(σ)}|edges(conv(a₁,…,aₙ) ∩ W)| ≤ 1 + E_{LG_d(σ,4√(d log n))}|edges(conv(a₁,…,aₙ) ∩ W)|
-- statement:
--   Let $n\ge d\ge3$, let $W$ be a fixed plane, $\bar a_1,\dots,\bar a_n\in\mathbb R^d$ and $\sigma>0$. Let $\mathbb E_{N_d(\sigma)}$ denote expectation over independent $a_i\sim N_d(\bar a_i,\sigma)$ and $\mathbb E_{LG_d(\sigma,r)}$ over independent $a_i\sim LG_d(\bar a_i,\sigma,r)$, with $r=4\sqrt{d\log n}$. Then the edge count is a.e. measurable under both laws and
--   $$\mathbb E_{N_d(\sigma)}\big[|\operatorname{edges}(\operatorname{conv}(a_1,\dots,a_n)\cap W)|\big]\ \le\ 1+\mathbb E_{LG_d(\sigma,r)}\big[|\operatorname{edges}(\operatorname{conv}(a_1,\dots,a_n)\cap W)|\big].$$
--
--   The Gaussian density is not log-Lipschitz, so Theorem 22 does not apply to it directly. This comparison transfers the Laplace–Gaussian bound to Gaussian perturbations at a cost of one edge.
--
--   **Formalization Note** The page's displayed formula writes $\operatorname{edges}(\operatorname{conv}(a_1,\dots,a_n))$, while its sentence and its proof (the bound $|\operatorname{edges}|\le\binom nd$) concern $\operatorname{conv}(a_1,\dots,a_n)\cap W$; the statement uses $\cap W$. The centers are arbitrary: the proof does not use their norms. $N_d(\bar a,\sigma)$ is the published Gaussian with density $(2\pi\sigma^2)^{-d/2}e^{-\|x-\bar a\|^2/(2\sigma^2)}$.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 46, p. 35 (proof pp. 35–36)

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 46 (p. 35). For `n ≥ d ≥ 3`, a fixed plane `W`, centers `ā₁, …, āₙ` and `σ > 0`, the
expected number of edges of `conv(a₁, …, aₙ) ∩ W` under independent Gaussian rows
`aᵢ ∼ N_d(āᵢ, σ)` is at most `1` plus the same expectation under independent Laplace–Gaussian
rows `aᵢ ∼ LG_d(āᵢ, σ, 4√(d log n))`. -/
theorem lemma_46 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (σ : ℝ) (hσ : 0 < σ) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ∧
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => lg (abar i) σ (4 * Real.sqrt (d * Real.log n)))) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ≤
      1 + ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => lg (abar i) σ (4 * Real.sqrt (d * Real.log n)))) := by sorry

end FriendlyShadow.Gaussian
