-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeLocal_unramified_marked_error_bound
-- name    : OAI.SevenEighths.ProbeLocal.unramified_marked_error_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:44:14.249704+00:00
-- url     : https://prove2.me/theorems/e0328879-c10b-45df-882a-0ba8fc7bb0b7
-- title:
--   Probe Local: unramified marked error bound
-- statement:
--   The Probe Local construction uses the unramified marked error bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/CorrectionBounds.lean#L24-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/CorrectionBounds.lean#L24-L54

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Local
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeLocal

theorem OAI.SevenEighths.ProbeLocal.unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by sorry
