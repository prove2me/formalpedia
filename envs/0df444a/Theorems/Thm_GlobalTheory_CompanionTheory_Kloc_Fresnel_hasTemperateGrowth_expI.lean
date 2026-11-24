-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_hasTemperateGrowth_expI
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.hasTemperateGrowth_expI
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:43.409+00:00
-- url     : https://prove2.me/theorems/7e7883d4-7c1c-404c-aa98-c9dca7eaf4e8
-- title:
--   Fresnel: has Temperate Growth exp I
-- statement:
--   The Fresnel construction uses the has Temperate Growth exp I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L9-L28

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

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by sorry
