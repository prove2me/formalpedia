-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_positive_rational_q_finite_family_has_integer_common_multiple
-- name    : OAI.PiExponent.LogarithmicJetIdeals.positive_rational_q_finite_family_has_integer_common_multiple
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T20:16:39.640924+00:00
-- url     : https://prove2.me/theorems/7bedc388-19d2-44a5-a1c8-aa62f98c7097
-- title:
--   Positive rational families have an integer common multiple
-- statement:
--   Every finite family of positive rational numbers has a positive rational common multiple whose ratio to each family member is a positive integer. For the empty family, any positive rational common multiple works.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem OAI.PiExponent.LogarithmicJetIdeals.positive_rational_q_finite_family_has_integer_common_multiple
    {n : ℕ} (q : Fin n → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ S : ℚ, 0 < S ∧ ∃ e : Fin n → ℕ, (∀ i, 0 < e i) ∧
      ∀ i, S = (e i : ℚ) * q i := by sorry
