-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_fourierInvCoord
-- name    : GlobalTheory.CompanionTheory.EisTube.fourierInvCoord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:21.516706+00:00
-- url     : https://prove2.me/theorems/e9636ff5-ff06-4710-8027-9d8d42a7dfc7
-- title:
--   Eis Tube: fourier Inv Coord
-- statement:
--   The Eis Tube construction uses the fourier Inv Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionFiniteDim.lean#L16-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionFiniteDim.lean#L16-L61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
universe u

theorem GlobalTheory.CompanionTheory.EisTube.fourierInvCoord : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y := by sorry
