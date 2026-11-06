-- Prove2me | Theorems.Thm_OAI_AnalyticBridge_weighted_fourier_minkowski_with_decay
-- name    : OAI.AnalyticBridge.weighted_fourier_minkowski_with_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:37.829434+00:00
-- url     : https://prove2.me/theorems/86104f8e-8d8d-47db-82e0-c232d7da9077
-- title:
--   Analytic Bridge: weighted fourier minkowski with decay
-- statement:
--   The Analytic Bridge construction uses the weighted fourier minkowski with decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L398-L422
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L398-L422

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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

theorem OAI.AnalyticBridge.weighted_fourier_minkowski_with_decay
    {Ω : Type*} (S : Finset Ω)
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ)
    (A J : ℕ) (R H C : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J)
    (hcoeff : (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C) :
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤ H * C := by sorry
