-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_19_levels_pos
-- name    : GaussLocalMaxColoring.Main.lemma_19_levels_pos
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:33:52.358208+00:00
-- url     : https://prove2.me/theorems/440d5707-07ea-4e69-90f6-045f92dd787f
-- title:
--   Lemma 19, second claim, for at least one level (corrected: the strict bound fails when $\ell=\lceil\log n\rceil=0$)
-- statement:
--   Source (Lemma 19, p. 18): if every set sampled at every level j = 1, ..., l has size less than T, then sum_{j=1}^{l} |F_{j-1} \ F_j| < 2lT/delta. Variant: the same conclusion under the additional hypothesis l >= 1 (that is, n >= 2). Difference: the source states the strict inequality also for l = 0, where both sides are 0.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 19, printed p. 18 (PDF 20) (corrected)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

theorem GaussLocalMaxColoring.Main.lemma_19_levels_pos {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hR : 1 ≤ R)
    (ω : Fin (GaussLocalMaxColoring.Main.numLevels n) × Fin R → Space d)
    (hℓ : 1 ≤ GaussLocalMaxColoring.Main.numLevels n) :
    (∀ j, 1 ≤ j → j ≤ GaussLocalMaxColoring.Main.numLevels n →
        ∀ i, (GaussLocalMaxColoring.Main.sampleSet G v δ ω j i).card < T) →
      (∑ j ∈ Finset.Icc 1 (GaussLocalMaxColoring.Main.numLevels n),
          ((GaussLocalMaxColoring.Main.cores G v δ ω (j - 1) \
            GaussLocalMaxColoring.Main.cores G v δ ω j).card : ℝ)) <
        2 * (GaussLocalMaxColoring.Main.numLevels n : ℝ) * T / δ := by sorry
