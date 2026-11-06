-- Prove2me | Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_weighted_normForm
-- name    : OAI.SevenEighths.LatticeSummability.summable_weighted_normForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:45.336346+00:00
-- url     : https://prove2.me/theorems/c15b99ec-5714-401d-918c-e88ae63c0783
-- title:
--   Lattice Summability: summable weighted norm Form
-- statement:
--   The Lattice Summability construction uses the summable weighted norm Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L74-L82
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L74-L82

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta

theorem OAI.SevenEighths.LatticeSummability.summable_weighted_normForm {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by sorry
