-- Prove2me | Theorems.Thm_HighDimStat_NonparametricLS_thm13_6_critical_radius_exists
-- name    : HighDimStat.NonparametricLS.thm13_6_critical_radius_exists
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:29:25.342974+00:00
-- url     : https://prove2.me/theorems/5a54f6cc-c1e5-4dec-a678-edd1ea3a38cd
-- title:
--   Monotonicity and existence of the critical radius (Lemma 13.6)
-- statement:
--   **Lemma 13.6** (p. 425). For any star-shaped function class $H$, the map
--   $\delta\mapsto G_n(\delta;H)/\delta$ is non-increasing on $(0,\infty)$. Consequently, for
--   any constant $c>0$, the inequality
--   $$
--   \frac{G_n(\delta;H)}{\delta}\le c\delta
--   $$
--   has a smallest positive solution.
--
--   This lemma is what makes sense of the phrase "let $\delta_n$ be any positive solution of
--   the critical inequality" in Theorems 13.5 and 13.13: it guarantees that valid radii exist
--   at all, and identifies the smallest one, $\delta_n^*$, as the natural choice.
--
--   **Formalization Note** $G_n$ is `localGaussianComplexity` from `HighDimStat.NonparametricLS.Core`.
--   The existence claim is stated as `IsLeast` of the solution set, matching "smallest
--   positive solution" literally.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 425 (PDF p. 445), Lemma 13.6

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Lemma 13.6** (p. 425, PDF 445). For any star-shaped function class `H`, the map
`δ ↦ Gₙ(δ; H)/δ` is non-increasing on `(0, ∞)`. Consequently, for any constant `c > 0`, the
inequality `Gₙ(δ; H)/δ ≤ cδ` has a smallest positive solution. -/
theorem thm13_6_critical_radius_exists {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hw : IsIIDStdGaussian P w)
    (H : Set (X → ℝ)) (hH : IsStarShaped H) :
    (∀ δ t : ℝ, 0 < δ → δ ≤ t →
        localGaussianComplexity x w P H t / t ≤ localGaussianComplexity x w P H δ / δ) ∧
      ∀ c : ℝ, 0 < c →
        ∃ δ, IsLeast {δ : ℝ | 0 < δ ∧ localGaussianComplexity x w P H δ / δ ≤ c * δ} δ := by sorry

end HighDimStat.NonparametricLS
