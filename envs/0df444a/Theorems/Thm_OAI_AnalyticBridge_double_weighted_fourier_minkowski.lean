-- Prove2me | Theorems.Thm_OAI_AnalyticBridge_double_weighted_fourier_minkowski
-- name    : OAI.AnalyticBridge.double_weighted_fourier_minkowski
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:33.069203+00:00
-- url     : https://prove2.me/theorems/2d86b4eb-a2de-477e-9bc9-cce23b00f493
-- title:
--   Analytic Bridge: double weighted fourier minkowski
-- statement:
--   The Analytic Bridge construction uses the double weighted fourier minkowski property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L130-L175
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L130-L175

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

theorem OAI.AnalyticBridge.double_weighted_fourier_minkowski
    {Ω : Type*} (S : Finset Ω)
    (b₁ b₂ : ℝ → ℂ) (φ : Ω → ℝ → ℝ → ℂ)
    (J₁ J₂ : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hinner : ∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ => b₂ t₂ * φ ω t₁ t₂) volume)
    (houter : ∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)) volume)
    (hweight₁ : Integrable
      (fun t₁ : ℝ => (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) volume)
    (hweight₂ : Integrable
      (fun t₂ : ℝ => (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) volume)
    (hφ : ∀ t₁ t₂ : ℝ,
      ‖∑ ω ∈ S, φ ω t₁ t₂‖ ≤
        H * (1 + ‖t₁‖) ^ J₁ * (1 + ‖t₂‖) ^ J₂) :
    ‖∑ ω ∈ S,
        ∫ t₁ : ℝ,
          b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
      H *
        (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
        (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) := by sorry
