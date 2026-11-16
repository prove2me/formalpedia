-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_7
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:25:26.077699+00:00
-- url     : https://prove2.me/theorems/cbdfdef7-0e2c-49f5-a8ed-384573c12059
-- title:
--   Lemma 6.7 — the canonical list is ε-close and has at most d+1 members
-- statement:
--   Let $\varepsilon>0$ and $p\in[0,1]^d$, and let $\mathcal L_p=\{R_u(p):u\in[0,\varepsilon)\}$. Then
--   1. every $y\in\mathcal L_p$ satisfies $\|y-p\|_\infty<\varepsilon$;
--   2. $|\mathcal L_p|\le d+1$.
--
--   The canonical list is the list witnessing $(d+1)$-list replicability of the upper-bound algorithms (Theorems 6.8, A.2), and its blockwise products give the lists of Theorem 6.13.
--
--   Differences from the source:
--   - encoding: the grid width ε of §6.2 (positive throughout §6) → hypothesis 0 < ε; reason: ε > 0 is the standing assumption of §6; for ε ≤ 0 the rounding is undefined
--   - encoding: vectors in ℝ^d with the ℓ∞ norm → functions Fin d → ℝ with their sup norm; reason: the same finite coordinates and the same distance
--   - encoding: |L_p| ≤ d + 1 → Set.encard (canonicalList ε p) ≤ d + 1; reason: extended cardinality; the bound also asserts that L_p is finite, as the source's |L_p| presupposes
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Definition 6.6 and Lemma 6.7, PDF p. 9

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.7, PDF p. 9 (with Definition 6.6), both clauses. Clause (2) is
stated with `Set.encard`, so it also asserts that L_p is finite. -/
theorem lemma_6_7 (ε : ℝ) (hε : 0 < ε) (d : ℕ) (p : Fin d → ℝ) (hp : p ∈ cube d 0 1) :
    (∀ y ∈ canonicalList ε p, ‖y - p‖ < ε) ∧
    (canonicalList ε p).encard ≤ (d : ℕ∞) + 1 := by sorry

end ListReplicableBias.LowerBound.Supplement
