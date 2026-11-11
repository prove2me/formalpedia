-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_2_2
-- name    : MemoSDPI.Main.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:09.566053+00:00
-- url     : https://prove2.me/theorems/8f2130f9-2b62-4d9e-83f7-eed9dba83af3
-- title:
--   Theorem 2.2 — a jointly Gaussian pair with correlation r satisfies an r²-SDPI
-- statement:
--   Let $(V, W)$ be jointly Gaussian real random variables with positive variances $\mathrm{Var}(V), \mathrm{Var}(W) > 0$ and correlation coefficient
--   $$
--   r \;=\; \frac{\mathrm{Cov}(V,W)}{\sqrt{\mathrm{Var}(V)\,\mathrm{Var}(W)}}.
--   $$
--   Then $(V, W)$ satisfies an $r^2$-SDPI: every Markov chain $V \to W \to U$ satisfies $I(U;V) \le r^2\, I(U;W)$.
--
--   This is the basic example of a strong data processing inequality (cited from Polyanskiy–Wu, Example 33.7); with tensorization it gives the SDPI of the Gaussian location model (Theorem 3.1).
--
--   **Formalization Note** The joint law $\mu$ of $(V,W)$ on $\mathbb R \times \mathbb R$ is a Gaussian measure in Mathlib's sense (`IsGaussian`: every continuous linear functional has a Gaussian law), which is joint Gaussianity. Variances and covariance are Mathlib's `Var[·; μ]` and `cov[·, ·; μ]` of the coordinate projections.
--
--   Differences from the source:
--   - encoding: (V, W) jointly Gaussian real random variables → a measure μ on ℝ × ℝ with IsGaussian μ (law of (V, W)); reason: the SDPI is a property of the joint law; IsGaussian on ℝ² is joint Gaussianity
--   - encoding: correlation coefficient r → cov[V, W; μ] / √(Var[V; μ] · Var[W; μ]); reason: definition of the correlation coefficient
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Theorem 2.2

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_SDPI

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Theorem 2.2 (cited from [PW24, Example 33.7]): a jointly Gaussian pair
`(V, W)` of real random variables with positive variances and correlation coefficient `r`
satisfies an `r²`-SDPI. -/
theorem theorem_2_2 (μ : Measure (ℝ × ℝ)) [IsGaussian μ]
    (hV : 0 < Var[fun p : ℝ × ℝ => p.1; μ]) (hW : 0 < Var[fun p : ℝ × ℝ => p.2; μ]) :
    SatisfiesSDPI μ
      ((cov[fun p : ℝ × ℝ => p.1, fun p : ℝ × ℝ => p.2; μ] /
          Real.sqrt (Var[fun p : ℝ × ℝ => p.1; μ] * Var[fun p : ℝ × ℝ => p.2; μ])) ^ 2) := by sorry

end MemoSDPI.Main
