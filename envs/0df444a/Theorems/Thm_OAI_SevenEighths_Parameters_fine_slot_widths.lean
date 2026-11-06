-- Prove2me | Theorems.Thm_OAI_SevenEighths_Parameters_fine_slot_widths
-- name    : OAI.SevenEighths.Parameters.fine_slot_widths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:35.546221+00:00
-- url     : https://prove2.me/theorems/da2e749f-c52d-4cbc-8897-9285fe19318f
-- title:
--   Parameters: fine slot widths
-- statement:
--   The Parameters construction uses the fine slot widths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersHighDataFine.lean#L78-L85
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersHighDataFine.lean#L78-L85

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighData
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighDataFine
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.Parameters

theorem OAI.SevenEighths.Parameters.fine_slot_widths {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0<mesh D.t)(hfine:∀j,D.ell j≤mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ)≤d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d≤mesh D.t:= by sorry
