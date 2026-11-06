-- Prove2me | Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_normForm_neg_rpow
-- name    : OAI.SevenEighths.LatticeSummability.summable_normForm_neg_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:43.936247+00:00
-- url     : https://prove2.me/theorems/8fb26b5e-a028-4e75-a057-0c747d77d8f5
-- title:
--   Lattice Summability: summable norm Form neg rpow
-- statement:
--   The Lattice Summability construction uses the summable norm Form neg rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L46-L67
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L46-L67

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta

theorem OAI.SevenEighths.LatticeSummability.summable_normForm_neg_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by sorry
