-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_nat_scalar_centers_pairwise_distinct
-- name    : OAI.PiExponent.LogarithmicJetIdeals.nat_scalar_centers_pairwise_distinct
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T22:37:33.451114+00:00
-- url     : https://prove2.me/theorems/497db431-658a-4c79-82f6-b2d207bb98a7
-- title:
--   Distinctness of natural scalar centers
-- statement:
--   A complex vector with a nonzero coordinate has distinct natural scalar multiples at distinct labels.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.nat_scalar_centers_pairwise_distinct
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (hr : ∃ i, r i ≠ 0) :
    ∀ j l : Fin K, j ≠ l → ∃ i : Fin m, (j.val : ℂ) * r i ≠ (l.val : ℂ) * r i := by sorry
