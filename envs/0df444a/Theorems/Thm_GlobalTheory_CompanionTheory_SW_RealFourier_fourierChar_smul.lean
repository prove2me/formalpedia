-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealFourier_fourierChar_smul
-- name    : GlobalTheory.CompanionTheory.SW.RealFourier.fourierChar_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:28.635799+00:00
-- url     : https://prove2.me/theorems/f01a9107-efc5-4afb-8696-8a1306d22ff6
-- title:
--   Real Fourier: fourier Char smul
-- statement:
--   The Real Fourier construction uses the fourier Char smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LebesgueSelfdualForDotCharacter.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LebesgueSelfdualForDotCharacter.lean#L11-L16

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LebesgueSelfdualForDotCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealFourier
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.RealFourier.fourierChar_smul (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by sorry
