-- Prove2me | Theorems.Thm_OAI_FourierBridge_coupled_double_log_separation
-- name    : OAI.FourierBridge.coupled_double_log_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:41.411451+00:00
-- url     : https://prove2.me/theorems/e79750c1-629e-4cbc-bf74-dc7afb387f22
-- title:
--   Fourier Bridge: coupled double log separation
-- statement:
--   The Fourier Bridge construction uses the coupled double log separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L54-L124
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L54-L124

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.FourierBridge
open scoped ContDiff FourierTransform SchwartzMap

theorem OAI.FourierBridge.coupled_double_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ V₁ V₂ : ℝ → ℂ)
    (R₁ R₂ : ℝ) (a₁ a₂ y : ι → ℝ)
    (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (hF₁s : ContDiff ℝ ∞ F₁)
    (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (hF₂s : ContDiff ℝ ∞ F₂)
    (hactive₁ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₁ (∑ j : ι, a₁ j * y j) = 1)
    (hactive₂ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₂ (∑ j : ι, a₂ j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
      F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
      ∫ t₁ : ℝ,
        (∫ t₂ : ℝ,
          (∏ j : ι,
            W j (y j) * logPhase t₁ (a₁ j * y j) *
              logPhase t₂ (a₂ j * y j)) *
            (𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)) t₂) *
          (𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)) t₁ := by sorry
