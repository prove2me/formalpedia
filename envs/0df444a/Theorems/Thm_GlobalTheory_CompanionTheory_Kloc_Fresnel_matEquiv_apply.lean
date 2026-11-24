-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_matEquiv_apply
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.matEquiv_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:48.669633+00:00
-- url     : https://prove2.me/theorems/e4a7cbba-c308-4e78-9ec7-1b053f2c61f0
-- title:
--   Fresnel: mat Equiv apply
-- statement:
--   The Fresnel construction uses the mat Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L338-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L338-L339

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
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.matEquiv_apply (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    matEquiv m n u p = u p.1 p.2 := by sorry
