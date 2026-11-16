-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_conditioning_log_concave
-- name    : IndependentInfoPricing.Main.Supplement.conditioning_log_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:52:55.751052+00:00
-- url     : https://prove2.me/theorems/169a8aa2-615d-4444-930a-84aa9688e055
-- title:
--   Lemma 4.9 — Conditioning preserves log-concavity
-- statement:
--   Let $v\in\mathbb R^Q$ have a law $F$ with a log-concave density $f$. Let $C\subseteq\mathbb R^Q$ be a convex set with $F(C)>0$. Then the conditional distribution of $v$ given $v\in C$ has a log-concave density. In particular, for every $i$,
--   $$V_i^+=\mathcal L\bigl(v_i\mid\Sigma(v)<0,\ v_i>0\bigr),\qquad V_i^-=\mathcal L\bigl(-v_i\mid\Sigma(v)>0,\ v_i<0\bigr)$$
--   have log-concave densities on $(0,\infty)$, whenever the respective conditioning event has positive probability (otherwise the conditional law is not defined).
--
--   Combined with the mean-tail bound (Lemma 4.10), this lets conditional-mean prices extract a constant fraction of the welfare on each half-space in the proof of Theorem 4.7.
--
--   **Formalization Note** Log-concavity is the published `LogConcaveOn` on the whole space (power form permitting zeros) for some measurable density version. "A log-concave density on $(0,\infty)$" is a density version that is log-concave on $\mathbb R$ and vanishes on $(-\infty,0]$, which for such a function is the same as log-concavity on $(0,\infty)$. The joint law need not be a product law, as in the source's lemma.
--
--   Differences from the source:
--   - encoding: the conditional law of v given C is log-concave; V_i^± have log-concave densities on (0,∞) → there is a measurable density version, log-concave on the whole space; for V_i^± it is log-concave on ℝ and zero on (−∞,0]; reason: a law is log-concave in the source's sense exactly when it has a log-concave density; for a function vanishing off (0,∞), log-concavity on ℝ in the zero-permitting form is log-concavity on (0,∞)
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.9, printed p.32 (PDF p.34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_LogConcave

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.9, p.32 (PDF 34): conditioning a log-concave law on a convex set of positive
probability keeps it log-concave; in particular `V_i⁺` and `V_i⁻` (when their conditioning
events have positive probability) have log-concave densities on `(0, ∞)`. -/
theorem conditioning_log_concave {Q : ℕ} (F : Measure (Values (Fin Q))) [IsProbabilityMeasure F]
    (hF : LogConcaveDensity F) :
    (∀ C : Set (Values (Fin Q)), Convex ℝ C → 0 < F C → LogConcaveDensity (conditionOn F C)) ∧
    ∀ i : Fin Q,
      (0 < F {v | ∑ j, v j < 0 ∧ 0 < v i} →
        ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x ≤ 0, g x = 0) ∧
          plusMagnitudeLaw F i = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
          ConvexOptimization.LogConcaveOn Set.univ g) ∧
      (0 < F {v | 0 < ∑ j, v j ∧ v i < 0} →
        ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x ≤ 0, g x = 0) ∧
          minusMagnitudeLaw F i = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
          ConvexOptimization.LogConcaveOn Set.univ g) := by sorry


end IndependentInfoPricing.Main.Supplement
