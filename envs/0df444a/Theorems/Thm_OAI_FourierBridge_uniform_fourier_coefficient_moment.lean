-- Prove2me | Theorems.Thm_OAI_FourierBridge_uniform_fourier_coefficient_moment
-- name    : OAI.FourierBridge.uniform_fourier_coefficient_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:03.870142+00:00
-- url     : https://prove2.me/theorems/0b14501a-6980-4288-9cf4-29366340a091
-- title:
--   Fourier Bridge: uniform fourier coefficient moment
-- statement:
--   The Fourier Bridge construction uses the uniform fourier coefficient moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L870-L907
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L870-L907

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

theorem OAI.FourierBridge.uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by sorry
