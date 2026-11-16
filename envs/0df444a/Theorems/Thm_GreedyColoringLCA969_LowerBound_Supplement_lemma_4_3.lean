-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_lemma_4_3
-- name    : GreedyColoringLCA969.LowerBound.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:55.649396+00:00
-- url     : https://prove2.me/theorems/4f24c934-6c52-47fc-8b3c-82a5b8151ff5
-- title:
--   Lemma 4.3 — A logarithmic-power quantile guarantee implies the full expectation bound E[X] ≤ 4(2t)^t.
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be any probability space, let $X:\Omega\to\mathbb R$ be a measurable nonnegative random variable, and let $t\ge1$ be an integer. Suppose for every $0<\varepsilon\le1/2$,
--
--   $$\Pr[X\le(\log_2(1/\varepsilon))^t]\ge1-\varepsilon.$$
--
--   Then its nonnegative extended expectation satisfies
--
--   $$\mathbb E[X]\le4(2t)^t.$$
--
--   The conclusion includes finiteness of the expectation; integrability is not assumed. This is the quantitative conversion needed for the finite-label upper bound.
--
--   Differences from the source:
--   - encoding: a nonnegative random variable and its expectation → a measurable nonnegative real-valued X on a probability space and its nonnegative extended integral; reason: measurability is part of being a random variable, and no integrability premise is added
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 15 (PDF 16), Lemma 4.3; proof pp.37–38 (PDF 38–39), Appendix B.1

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hnonneg : ∀ ω, 0 ≤ X ω) (t : ℕ) (ht : 1 ≤ t)
    (htail : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ μ {ω | X ω ≤ (log2 (1 / ε))^t}) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ≤ ENNReal.ofReal (4 * (2 * (t : ℝ))^t) := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
