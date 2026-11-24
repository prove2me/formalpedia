-- Prove2me | Theorems.Thm_MeasureTheory_exists_measurableSet_nonmeasurable_fst_image
-- name    : MeasureTheory.exists_measurableSet_nonmeasurable_fst_image
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:29:54.476599+00:00
-- url     : https://prove2.me/theorems/7042149d-2a37-46b9-8280-3c85be2f21d4
-- title:
--   Existence of a Borel set in $\mathbb{R}\\times\mathbb{R}_{\\ge 0}$ with non-Borel projection
-- statement:
--   There exists a Borel-measurable set $E\subseteq\mathbb{R}\times\mathbb{R}_{\ge 0}$ whose projection onto the first factor is not Borel-measurable.
--
--   This is Suslin's classical correction of Lebesgue: projections of Borel sets are analytic, and some analytic sets fail to be Borel. It is the standard engine for counterexamples to Borel measurability of debut/hitting times under mere joint measurability.
-- source:
--   Suslin 1917; Kechris Classical Descriptive Set Theory, Thm. 14.2 / projection of Borel sets

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

theorem MeasureTheory.exists_measurableSet_nonmeasurable_fst_image :
    ∃ E : Set (ℝ × ℝ≥0), MeasurableSet E ∧ ¬ MeasurableSet (Prod.fst '' E) := by
  sorry
