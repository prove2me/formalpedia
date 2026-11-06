-- Prove2me | Theorems.Thm_OAI_FourierBridge_exists_complex_smooth_cutoff
-- name    : OAI.FourierBridge.exists_complex_smooth_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:00.673759+00:00
-- url     : https://prove2.me/theorems/84c96ade-d67a-44f1-9f98-5fb3c93fa2a4
-- title:
--   Fourier Bridge: exists complex smooth cutoff
-- statement:
--   The Fourier Bridge construction uses the exists complex smooth cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1229-L1268
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1229-L1268

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge

theorem OAI.FourierBridge.exists_complex_smooth_cutoff (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ,
      HasCompactSupport V ∧
      ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧
      V 0 = 1 := by sorry
