-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelComposition_integral_shifted_eq_ker_cv
-- name    : GlobalTheory.CompanionTheory.KernelComposition.integral_shifted_eq_ker_cv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:46.785504+00:00
-- url     : https://prove2.me/theorems/1a8b4ae0-8702-4607-a66b-8741fe63543b
-- title:
--   Kernel Composition: integral shifted eq ker cv
-- statement:
--   The Kernel Composition construction uses the integral shifted eq ker cv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L40-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L40-L74

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerMulOfKerBasicOfCvTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelComposition

theorem GlobalTheory.CompanionTheory.KernelComposition.integral_shifted_eq_ker_cv (hc : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, φ z * ker X.Γ ψ (x * z) y ∂X.μ = ker X.Γ (cv X.μ φ ψ) x y := by sorry
