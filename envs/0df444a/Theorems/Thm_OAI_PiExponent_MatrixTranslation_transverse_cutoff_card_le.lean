-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslation_transverse_cutoff_card_le
-- name    : OAI.PiExponent.MatrixTranslation.transverse_cutoff_card_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T10:01:10.386364+00:00
-- url     : https://prove2.me/theorems/59e03668-fb0f-4d74-a946-3c0b5b77c978
-- title:
--   Weighted cutoff capacity for transverse indices
-- statement:
--   For any finite family of strictly positive weights, the transverse indices from a simplex with cutoff H that also satisfy total weight at most B are counted by the weighted simplex with cutoff B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L133-L153

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslation.transverse_cutoff_card_le {m : ℕ}
    (w : Fin m → ℝ) (H B : ℝ) (hw : ∀ i, 0 < w i) :
    ((Finset.univ : Finset (↥(OAI.PiExponent.MatrixTranslation.transverseIndices w H))).filter
      (fun a => ∑ i, w i * (a.1 i : ℝ) ≤ B)).card ≤
      (OAI.PiExponent.realWeightedSimplex w B).card := by
  sorry
