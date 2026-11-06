-- Prove2me | Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_one_div_normForm_rpow
-- name    : OAI.SevenEighths.LatticeSummability.summable_one_div_normForm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:49.64139+00:00
-- url     : https://prove2.me/theorems/f9493a79-0c9e-4ba9-99b3-599a87eb937f
-- title:
--   Lattice Summability: summable one div norm Form rpow
-- statement:
--   The Lattice Summability construction uses the summable one div norm Form rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L69-L72
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L69-L72

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta

theorem OAI.SevenEighths.LatticeSummability.summable_one_div_normForm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by sorry
