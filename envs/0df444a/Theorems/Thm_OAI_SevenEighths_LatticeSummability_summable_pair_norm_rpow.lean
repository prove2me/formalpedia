-- Prove2me | Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_pair_norm_rpow
-- name    : OAI.SevenEighths.LatticeSummability.summable_pair_norm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:38.809197+00:00
-- url     : https://prove2.me/theorems/c7f5304b-5470-4b9a-8d16-82561c4bb6f5
-- title:
--   Lattice Summability: summable pair norm rpow
-- statement:
--   The Lattice Summability construction uses the summable pair norm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L36-L44
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean#L36-L44

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta

theorem OAI.SevenEighths.LatticeSummability.summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by sorry
