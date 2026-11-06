-- Prove2me | Theorems.Thm_OAI_SevenEighths_Parameters_exists_high_data_fine
-- name    : OAI.SevenEighths.Parameters.exists_high_data_fine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:42.588636+00:00
-- url     : https://prove2.me/theorems/c9908f95-b6af-470f-9dde-9e17ca5cef7c
-- title:
--   Parameters: exists high data fine
-- statement:
--   The Parameters construction uses the exists high data fine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersHighDataFine.lean#L10-L76
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersHighDataFine.lean#L10-L76

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighData
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighDataFine
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.Parameters

theorem OAI.SevenEighths.Parameters.exists_high_data_fine (Δ:ℝ)(hΔ:0<Δ)(mesh:ℝ→ℝ)
    (hmesh:∀t:ℝ,0<t→0<mesh t):
    ∃D:HighData Δ,∀j,D.ell j≤mesh D.t/200:= by sorry
