-- Prove2me | Theorems.Thm_OAI_FourierBridge_coupled_log_separation_schwartz
-- name    : OAI.FourierBridge.coupled_log_separation_schwartz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:30:59.552429+00:00
-- url     : https://prove2.me/theorems/cba74aae-ff71-40a9-a3fc-b9a3354e08ad
-- title:
--   Fourier Bridge: coupled log separation schwartz
-- statement:
--   The Fourier Bridge construction uses the coupled log separation schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1475-L1550
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1475-L1550

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

theorem OAI.FourierBridge.coupled_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : 𝓢(ℝ, ℂ)) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ (b : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
              b R t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b R t‖) ≤ C := by sorry
