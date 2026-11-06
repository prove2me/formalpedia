-- Prove2me | Theorems.Thm_OAI_FourierBridge_logProfile_coefficient_moment
-- name    : OAI.FourierBridge.logProfile_coefficient_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:30:01.713199+00:00
-- url     : https://prove2.me/theorems/b28742a1-aeec-42b1-b9cd-71d11a38a647
-- title:
--   Fourier Bridge: log Profile coefficient moment
-- statement:
--   The Fourier Bridge construction uses the log Profile coefficient moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L471-L483
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L471-L483

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

theorem OAI.FourierBridge.logProfile_coefficient_moment
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0)
          (𝓕 (logProfile W F R a hWc hWs hFs)) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0)
          (𝓕 (logProfile W F R a hWc hWs hFs))) := by sorry
