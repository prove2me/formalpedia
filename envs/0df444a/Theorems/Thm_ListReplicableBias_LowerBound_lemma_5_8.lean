-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_5_8
-- name    : ListReplicableBias.LowerBound.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:43.651059+00:00
-- url     : https://prove2.me/theorems/7c7a319e-e963-444c-a1ec-8d2ebb3abbac
-- title:
--   Lemma 5.8 — Separation of accurate output lists
-- statement:
--   Let $\varepsilon>0$ and $p,q\in[0,1]^d$. Let $L_p,L_q$ be finite output lists whose members are $\varepsilon$-close to their respective bias vectors. Then, for every $y\in L_p$,
--   $$\|p-q\|_\infty>2\varepsilon\quad\Longrightarrow\quad y\notin L_q.$$
--   The result applies in particular to the source's most likely output $y_p$. It isolates the geometric separation property of accurate lists.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - generalization: the most likely member of lists from a list-replicable algorithm in the regime epsilon,delta in (0,1/8) → every member of any two finite epsilon-accurate lists for every epsilon>0, without a probability or cardinality premise; reason: the source lists and most likely member are instances; the page explicitly argues using only accuracy and separation
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 5.8, PDF p. 6

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma 5.8, PDF p. 6, for every member of every accurate list. -/
theorem lemma_5_8 {d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (p q : Fin d → ℝ) (hp : p ∈ cube d 0 1) (hq : q ∈ cube d 0 1)
    (Lp Lq : Finset (Fin d → ℝ))
    (hLp : ∀ y ∈ Lp, ‖y - p‖ ≤ ε) (hLq : ∀ y ∈ Lq, ‖y - q‖ ≤ ε)
    (y : Fin d → ℝ) (hy : y ∈ Lp) (hpq : 2 * ε < ‖p - q‖) :
    y ∉ Lq := by sorry

end ListReplicableBias.LowerBound
