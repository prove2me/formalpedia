-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_5_9
-- name    : ListReplicableBias.LowerBound.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:05.699942+00:00
-- url     : https://prove2.me/theorems/03cb17d2-569e-428f-a97d-d18e4e404e5d
-- title:
--   Lemma 5.9 — Accurate output selections color the central cube
-- statement:
--   Let $0<\varepsilon<1/8$ and $R=[1/2-2\varepsilon,1/2+2\varepsilon]^d$. Let $\chi:\mathbb R^d\to\mathbb R^d$ satisfy $\|\chi(p)-p\|_\infty\le\varepsilon$ for every $p\in R$. Then
--   $$\chi|_R\text{ is a Sperner/KKM coloring of }R.$$
--   Thus the most likely accurate-output selection in the paper has the required coloring property; no measurability of the selection is required.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - generalization: the most likely list-output coloring from a list-replicable algorithm → every epsilon-close selection on the central cube, without any probabilistic premise; reason: the source selection is epsilon-close, and the face-separation argument uses only this property
--   - encoding: a map defined on R → an ambient map with the accuracy assumption only on R; reason: restriction and extension preserve the face rule and all relevant instances
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 5.9, PDF p. 6

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma 5.9, PDF p. 6: every ε-close selection has the claimed face rule. -/
theorem lemma_5_9 {d : ℕ} (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 8))
    (χ : (Fin d → ℝ) → (Fin d → ℝ))
    (hχ : ∀ p ∈ region d ε, ‖χ p - p‖ ≤ ε) :
    IsSpernerKKMColoring (1 / 2 - 2 * ε) (1 / 2 + 2 * ε) χ := by sorry

end ListReplicableBias.LowerBound
