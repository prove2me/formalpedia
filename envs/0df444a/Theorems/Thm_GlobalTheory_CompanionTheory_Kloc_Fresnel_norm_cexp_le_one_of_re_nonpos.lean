-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_norm_cexp_le_one_of_re_nonpos
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.norm_cexp_le_one_of_re_nonpos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:42.991928+00:00
-- url     : https://prove2.me/theorems/0e4c9f4f-25bf-4c14-ac54-6ddf5ffa1548
-- title:
--   Fresnel: norm cexp le one of re nonpos
-- statement:
--   The Fresnel construction uses the norm cexp le one of re nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L106-L107

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

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.norm_cexp_le_one_of_re_nonpos {z : ℂ} (h : z.re ≤ 0) : ‖cexp z‖ ≤ 1 := by sorry
