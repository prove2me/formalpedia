-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_integral_gauss_kerOp
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.integral_gauss_kerOp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:26.152166+00:00
-- url     : https://prove2.me/theorems/96f9ad24-7b5e-4e98-8971-8d304ee5d477
-- title:
--   Fresnel: integral gauss ker Op
-- statement:
--   The Fresnel construction uses the integral gauss ker Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L130-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L130-L177

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

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.integral_gauss_kerOp (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re)
    (f : 𝓢(V, ℂ)) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t =
      C * (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        ∫ v : V, f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by sorry
