-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_3
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:48.145678+00:00
-- url     : https://prove2.me/theorems/5e8dc4ba-ca01-4b56-95d7-7f5234d75712
-- title:
--   Lemma 6.3 — shifted rounding moves by strictly less than ε
-- statement:
--   Let $u\in[0,\varepsilon)$. For every $x\in\mathbb R$,
--   $$|R_u(x)-x|<\varepsilon,$$
--   and for every $d$ and every $x\in\mathbb R^d$,
--   $$\|R_u(x)-x\|_\infty<\varepsilon .$$
--
--   This is the accuracy of rounding: every member of the canonical list is strictly $\varepsilon$-close to the bias vector (Lemma 6.7).
--
--   Differences from the source:
--   - encoding: vectors in ℝ^d with the ℓ∞ norm → functions Fin d → ℝ with their sup norm; reason: the same finite coordinates and the same distance
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 6.3, PDF p. 8

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.3, PDF p. 8: u-rounding moves a real, and a vector in sup norm, by
strictly less than ε. -/
theorem lemma_6_3 (ε u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) ε) :
    (∀ x : ℝ, |roundShift ε u x - x| < ε) ∧
    (∀ (d : ℕ) (x : Fin d → ℝ), ‖roundVec ε u x - x‖ < ε) := by sorry

end ListReplicableBias.LowerBound.Supplement
