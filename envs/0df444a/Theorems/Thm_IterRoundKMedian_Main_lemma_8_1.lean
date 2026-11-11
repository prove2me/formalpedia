-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_lemma_8_1
-- name    : IterRoundKMedian.Main.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:27:10.107572+00:00
-- url     : https://prove2.me/theorems/656668f4-6f11-447b-9dd6-12cbc63bb04f
-- title:
--   Lemma 8.1 — the cheaper of the two roundings has E[cost(O)] ≤ (1 + ρ)α⋆V with α⋆ = 2 − β⋆/12 ≈ 1.99984
-- statement:
--   Let $\rho\in(0,1]$. For every client $j$ of a finite client set let $x_{ij}\ge0$ with $\sum_ix_{ij}=1$ and distances $d(i,j)\ge0$ define $V_j$, $D_j$, $M_j$ (as in `ClientProfile`), and put $V=\sum_jV_j$. On one probability space let $c^{(1)}_j,c^{(2)}_j\ge0$ be integrable random variables (the connection costs $d(j,O_1)$, $d(j,O_2)$) with
--   $$\mathbb E[c^{(1)}_j]\le(1+\rho)\Big(2V_j-\frac{D_j}{12}\Big)\ \ (90),\qquad \mathbb E[c^{(2)}_j]\le\Big(1+\frac2e\Big)V_j+\sqrt{\frac{90V_jM_j}{e}}+\frac{15}{2}M_j\ \ (91).$$
--   Let $\mathrm{cost}(O)=\min\{\sum_jc^{(1)}_j,\sum_jc^{(2)}_j\}$ be the cost of the cheaper set. Then
--   $$\mathbb E[\mathrm{cost}(O)]\ \le\ (1+\rho)\,\alpha_\star V,$$
--   with $\alpha_\star=2-\beta_\star/12$ from (92), and numerically $\beta_\star\approx0.00188669438974$, $\alpha_\star\approx1.99984277546752$.
--
--   This is the combination step of §8: the dispersion-aware conversion and the robust rounding are each worse than $\alpha_\star$ on some clients, but never simultaneously.
--
--   Differences from the source:
--
--   - generalization: d(j, O_1), d(j, O_2) for the random sets returned by Algorithm 6.1 and by Theorem 7.1's algorithm; O the cheaper set → any nonnegative integrable random variables c₁ j, c₂ j on one probability space satisfying (90) and (91); cost(O) = min of the two sums; reason: the proof uses only (90), (91) and that O is the pointwise cheaper set
--   - generalization: V_j, D_j, M_j from the accepted preprocessed complete solution → V_j, D_j, M_j from any weights x_ij ≥ 0 with Σ_i x_ij = 1 and distances ≥ 0; reason: the proof uses only M_j ≤ D_j ≤ 2V_j, which hold for every such profile
--   - encoding: expectations of the costs → Bochner integrals with Integrable hypotheses; reason: the costs are bounded in the source (finite metric), so the hypothesis only excludes undefined expectations
--   - reading: Numerically, β⋆ ≈ 0.00188669438974 and α⋆ ≈ 1.99984277546752 → |β⋆ − 0.00188669438974| ≤ 5·10⁻¹⁵ and |α⋆ − 1.99984277546752| ≤ 5·10⁻¹⁵; reason: ≈ read as correct to the printed digits (within half a unit of the last printed digit)
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 71, Lemma 8.1 and (90)–(92)

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_ClientProfile
import Definitions.Def_IterRoundKMedian_Main_Combination

namespace IterRoundKMedian.Main

open MeasureTheory ClientProfile Combination in
theorem lemma_8_1 {C ι Ω : Type*} [Fintype C] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x dist : C → ι → ℝ) (hx : ∀ j i, 0 ≤ x j i) (hx1 : ∀ j, ∑ i, x j i = 1)
    (hdist : ∀ j i, 0 ≤ dist j i)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (c₁ c₂ : C → Ω → ℝ) (hc₁ : ∀ j ω, 0 ≤ c₁ j ω) (hc₂ : ∀ j ω, 0 ≤ c₂ j ω)
    (hi₁ : ∀ j, Integrable (c₁ j) P) (hi₂ : ∀ j, Integrable (c₂ j) P)
    (h90 : ∀ j, ∫ ω, c₁ j ω ∂P ≤ (1 + ρ) * (2 * V (x j) (dist j) - D (x j) (dist j) / 12))
    (h91 : ∀ j, ∫ ω, c₂ j ω ∂P ≤ (1 + 2 / Real.exp 1) * V (x j) (dist j)
      + Real.sqrt (90 * V (x j) (dist j) * M (x j) (dist j) / Real.exp 1)
      + 15 / 2 * M (x j) (dist j)) :
    ∫ ω, min (∑ j, c₁ j ω) (∑ j, c₂ j ω) ∂P ≤ (1 + ρ) * alphaStar * ∑ j, V (x j) (dist j) ∧
      |betaStar - 0.00188669438974| ≤ 5e-15 ∧ |alphaStar - 1.99984277546752| ≤ 5e-15 := by sorry

end IterRoundKMedian.Main
