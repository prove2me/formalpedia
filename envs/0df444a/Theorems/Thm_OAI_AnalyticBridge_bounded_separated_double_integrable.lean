-- Prove2me | Theorems.Thm_OAI_AnalyticBridge_bounded_separated_double_integrable
-- name    : OAI.AnalyticBridge.bounded_separated_double_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:54.800121+00:00
-- url     : https://prove2.me/theorems/cba6bf0c-690f-49f2-983d-f3a5adb106c6
-- title:
--   Analytic Bridge: bounded separated double integrable
-- statement:
--   The Analytic Bridge construction uses the bounded separated double integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L196-L259
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L196-L259

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
open OAI.AnalyticBridge
open scoped FourierTransform SchwartzMap

theorem OAI.AnalyticBridge.bounded_separated_double_integrable
    {Ω : Type*} (S : Finset Ω)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (u v : Ω → ℝ → ℂ)
    (humeas : ∀ ω ∈ S, AEStronglyMeasurable (u ω) volume)
    (hvmeas : ∀ ω ∈ S, AEStronglyMeasurable (v ω) volume)
    (hubdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖u ω t‖ ≤ M)
    (hvbdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖v ω t‖ ≤ M) :
    (∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ =>
        (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) volume) ∧
    (∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        (𝓕 g₁) t₁ *
          (∫ t₂ : ℝ,
            (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂))) volume) := by sorry
