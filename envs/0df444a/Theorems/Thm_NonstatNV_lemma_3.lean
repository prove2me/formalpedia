-- Prove2me | Theorems.Thm_NonstatNV_lemma_3
-- name    : NonstatNV.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:35.815019+00:00
-- url     : https://prove2.me/theorems/998e90ff-cecc-4aa2-b229-cf859f767852
-- title:
--   Lemma 3 (Hoeffding's inequality) — $\mathbb P(\frac1n|\sum\epsilon_i|>t)\le2e^{-nt^2/(CK^2)}$ with $C\le144e$
-- statement:
--   Let $\epsilon_1,\dots,\epsilon_n$ ($n\ge1$) be independent, mean-zero random variables on a probability space, sub-Gaussian with sub-Gaussian norm at most $K>0$ in the sense
--
--   $$
--   \mathbb P(|\epsilon_i|>t)\le 2\exp\!\left(-\frac{t^2}{K^2}\right)\qquad\text{for all } t\ge0 .
--   $$
--
--   Then
--
--   $$
--   \mathbb P\left(\frac1n\Big|\sum_{i=1}^{n}\epsilon_i\Big|>t\right)\le 2\exp\!\left(-\frac{n t^2}{144e\,K^2}\right)\qquad\text{for all } t\ge0 .
--   $$
--
--   This is the concentration inequality behind the window estimates of the Fixed-Time-Window Policy and the good event in the analysis of PERP.
--
--   **Formalization Note** The variables are measurable functions on an arbitrary probability space, independent as a family; the tail hypothesis is stated for the law of each $\epsilon_i$.
--
--   Differences from the source:
--   - encoding: for some universal constant C, … ≤ 2exp(−nt²/(CK²)); moreover C ≤ 144e → the bound with C = 144e; reason: the right side increases with C, so the bound with some C ≤ 144e is equivalent to the bound with C = 144e
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Lemma 3, p.35

import Definitions.Def_NonstatNV_IsTailSubGaussian

open MeasureTheory ProbabilityTheory

namespace NonstatNV

/-- **Lemma 3 (Hoeffding's Inequality)** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.35). Let `ε₁, …, εₙ` be independent, mean-zero,
sub-Gaussian random variables with sub-Gaussian norm at most `K`:
`P(|εᵢ| > t) ≤ 2 exp(−t²/K²)` for all `t ≥ 0`. Then
`P((1/n)|Σᵢ εᵢ| > t) ≤ 2 exp(−n t²/(C K²))` for all `t ≥ 0`, with `C ≤ 144e`.

**Formalization Note** Stated with `C = 144e`, which is equivalent because the right side increases
with `C`. The variables live on an arbitrary probability space; `n ≥ 1` and `K > 0`. The tail
hypothesis is `IsTailSubGaussian` of the law of `εᵢ`; the strict inequalities are the printed ones. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (K : ℝ) (hK : 0 < K) (ε : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i)) (hind : iIndepFun ε P) (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0)
    (htail : ∀ i, IsTailSubGaussian (P.map (ε i)) K) :
    ∀ t : ℝ, 0 ≤ t →
      P {ω | t < |(1 / (n : ℝ)) * ∑ i, ε i ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * t ^ 2) / (144 * Real.exp 1 * K ^ 2))) := by sorry

end NonstatNV
