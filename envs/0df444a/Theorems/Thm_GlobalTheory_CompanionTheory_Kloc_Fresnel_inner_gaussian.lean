-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_inner_gaussian
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.inner_gaussian
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:33.574436+00:00
-- url     : https://prove2.me/theorems/abb40325-25bb-4c63-bb3b-3e5d1ec6b7b8
-- title:
--   Fresnel: inner gaussian
-- statement:
--   The Fresnel construction uses the inner gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L109-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L109-L128

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.inner_gaussian (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re) (v : V) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by sorry
