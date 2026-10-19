-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_disjoint
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_disjoint
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:24:14.409213+00:00
-- url     : https://prove2.me/theorems/d5f3a7ee-32b5-4393-b498-05e5c860d670
-- title:
--   Distinct weighted lattice boxes are disjoint
-- statement:
--   Boxes indexed by distinct vectors are disjoint. Since `a ≠ b`, choose a coordinate with different natural values. Order the two values and use positivity of the weight to show the upper endpoint of the earlier half-open interval is at most the lower endpoint of the later interval, contradicting membership in both boxes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_disjoint
    (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (a b : Fin m → ℕ) (hab : a ≠ b) :
    Disjoint
      {x : Fin m → ℝ | ∀ i,
        w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)}
      {x : Fin m → ℝ | ∀ i,
        w i * (b i : ℝ) ≤ x i ∧ x i < w i * ((b i : ℝ) + 1)} := by sorry
