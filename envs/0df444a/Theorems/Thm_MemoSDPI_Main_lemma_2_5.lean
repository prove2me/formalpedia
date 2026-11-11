-- Prove2me | Theorems.Thm_MemoSDPI_Main_lemma_2_5
-- name    : MemoSDPI.Main.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:17.670662+00:00
-- url     : https://prove2.me/theorems/2af65d44-bed4-4f23-9921-2855168e1ad1
-- title:
--   Lemma 2.5 — an η-SDPI survives independent randomized maps of the two sides
-- statement:
--   Let $\eta\in[0,1]$ and suppose that $(V, W)$ satisfies an $\eta$-SDPI. Let
--   $$
--   V' = f(V, R_1), \qquad W' = g(W, R_2)
--   $$
--   for maps $f$ and $g$, where $R_1$, $R_2$ and $(V, W)$ are mutually independent. Then $(V', W')$ satisfies an $\eta$-SDPI.
--
--   The lemma passes from the sample mean to the whole sample (Theorem 3.1) and from Gaussian to thresholded observations (Theorem 3.3).
--
--   **Formalization Note** $(V,W)$ has joint law $\mu$, $R_1 \sim \nu_1$ and $R_2 \sim \nu_2$ on arbitrary measurable spaces, and mutual independence is the product law $\mu \otimes \nu_1 \otimes \nu_2$; the law of $(V', W')$ is its pushforward under $((v,w),(r_1,r_2)) \mapsto (f(v,r_1), g(w,r_2))$ with $f, g$ measurable.
--
--   Differences from the source:
--   - encoding: maps f and g → measurable maps f : V × R₁ → V′, g : W × R₂ → W′; reason: V′ and W′ are random variables only for measurable maps
--   - encoding: R₁, R₂ and (V, W) mutually independent → law μ ⊗ (ν₁ ⊗ ν₂) of ((V, W), (R₁, R₂)); reason: definition of mutual independence
--   - encoding: η ∈ [0, 1] (Definition 2.1) → hypotheses 0 ≤ η and η ≤ 1; reason: the range is part of Definition 2.1
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Lemma 2.5

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_SDPI

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Lemma 2.5: if `(V, W)` satisfies an `η`-SDPI, `V′ = f(V, R₁)` and
`W′ = g(W, R₂)` with `R₁`, `R₂` and `(V, W)` mutually independent, then `(V′, W′)` satisfies an
`η`-SDPI. -/
theorem lemma_2_5 {V W V' W' R₁ R₂ : Type} [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSpace V'] [MeasurableSpace W'] [MeasurableSpace R₁] [MeasurableSpace R₂]
    (μ : Measure (V × W)) [IsProbabilityMeasure μ]
    (ν₁ : Measure R₁) [IsProbabilityMeasure ν₁] (ν₂ : Measure R₂) [IsProbabilityMeasure ν₂]
    (f : V × R₁ → V') (g : W × R₂ → W') (hf : Measurable f) (hg : Measurable g)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (h : SatisfiesSDPI μ η) :
    SatisfiesSDPI
      ((μ.prod (ν₁.prod ν₂)).map
        (fun x : (V × W) × (R₁ × R₂) => (f (x.1.1, x.2.1), g (x.1.2, x.2.2)))) η := by sorry

end MemoSDPI.Main
