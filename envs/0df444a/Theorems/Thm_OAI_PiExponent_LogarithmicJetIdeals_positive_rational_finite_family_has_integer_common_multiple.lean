-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_positive_rational_finite_family_has_integer_common_multiple
-- name    : OAI.PiExponent.LogarithmicJetIdeals.positive_rational_finite_family_has_integer_common_multiple
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T19:06:50.376143+00:00
-- url     : https://prove2.me/theorems/2c9caefd-6ce3-4056-907e-3fdbacba35aa
-- title:
--   Positive rational families have an integer common multiple
-- statement:
--   Any finite family of positive rational real numbers has a common positive real multiple whose ratio to each family member is a positive integer. The result also covers the empty family, although the target family is nonempty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem OAI.PiExponent.LogarithmicJetIdeals.positive_rational_finite_family_has_integer_common_multiple
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hwr : ∀ i, ∃ q : ℚ, w i = (q : ℝ)) :
    ∃ S : ℝ, 0 < S ∧ ∃ e : Fin n → ℕ, (∀ i, 0 < e i) ∧
      ∀ i, S = (e i : ℝ) * w i := by sorry
