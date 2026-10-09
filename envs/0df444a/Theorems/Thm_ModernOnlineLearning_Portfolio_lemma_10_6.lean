-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_6
-- name    : ModernOnlineLearning.Portfolio.lemma_10_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:39.380982+00:00
-- url     : https://prove2.me/theorems/a2775f5d-e2a4-4ea2-855e-17b708d79419
-- title:
--   Lemma 10.6, pp. 174–175 — reduce the wealth ratio to single-stock market paths
-- statement:
--   Let $d\ge2$, $T\ge1$, and let $F$ be a probability measure concentrated on the portfolio simplex $\Delta^{d-1}$. Let $w_1,\ldots,w_T$ be nonnegative, nonzero market vectors for which Algorithm 10.1 is defined, i.e. its normalizing integral $\int_{\Delta^{d-1}}W_{t-1}(x)\,F(dx)$ is positive in every round $t=1,\ldots,T$. Then for every fixed portfolio $u\in\Delta^{d-1}$, with $W_T$ the wealth of Algorithm 10.1,
--
--   $$\frac{W_T(u)}{W_T}\le\max_{j\in\{1,\ldots,d\}^{T}}\frac{\prod_{t=1}^{T}u_{j_t}}{\int_{\Delta^{d-1}}\prod_{t=1}^{T}x_{j_t}\,F(dx)}.$$
--
--   This comparison removes the market gains from the bound and leaves finitely many monomial ratios to analyze.
--
--   **Formalization Note** Both quotients are taken in the extended nonnegative reals with $a/0=+\infty$ for $a>0$ and $0/0=0$, the convention of Lemma 10.5 that the book's proof applies; a path whose prior moment is zero thus contributes $+\infty$ or $0$. The positivity of the normalizing integrals is not printed in the lemma but is needed for line 3 of Algorithm 10.1 to define $x_t$; it is stated as a hypothesis. The prior is a probability measure concentrated on the simplex. Stock choices use `Fin T` internally, equivalent to the book’s positions $1,\ldots,T$.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 10.6, pp. 174–175

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Lemma 10.6, pp. 174-175. The ratios are in `ENNReal`, which realizes the
conventions `a/0 = +∞` for `a > 0` and `0/0 = 0` of Lemma 10.5 used in the proof.
`hden` says that line 3 of Algorithm 10.1 is defined in every round `1, …, T`. -/
theorem lemma_10_6 {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (F : MeasureTheory.Measure (Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure F]
    (hF : F (stdSimplex ℝ (Fin d))ᶜ = 0)
    (w : ℕ → Fin d → ℝ)
    (hw_nonneg : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ w t i)
    (hw_ne : ∀ t ∈ Finset.Icc 1 T, w t ≠ 0)
    (hden : ∀ t ∈ Finset.Icc 1 T, 0 < ∫ p, wealthBefore w p t ∂F)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ENNReal.ofReal (wealthCRP w u T) /
        ENNReal.ofReal (portfolioWealth w (weightedPortfolio F w) T) ≤
      ⨆ j : Fin T → Fin d,
        ENNReal.ofReal (sequenceMonomial j u) /
          ENNReal.ofReal (∫ p, sequenceMonomial j p ∂F) := by sorry

end ModernOnlineLearning.Portfolio
