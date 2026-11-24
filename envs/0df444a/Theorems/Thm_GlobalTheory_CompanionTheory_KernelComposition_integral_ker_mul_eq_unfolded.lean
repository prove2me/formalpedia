-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelComposition_integral_ker_mul_eq_unfolded
-- name    : GlobalTheory.CompanionTheory.KernelComposition.integral_ker_mul_eq_unfolded
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:30.151649+00:00
-- url     : https://prove2.me/theorems/317fa61c-e6b0-47e8-9cc4-13accc98e95b
-- title:
--   Kernel Composition: integral ker mul eq unfolded
-- statement:
--   The Kernel Composition construction uses the integral ker mul eq unfolded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L9-L38

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

theorem GlobalTheory.CompanionTheory.KernelComposition.integral_ker_mul_eq_unfolded (hk : KerBasic) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ∫ z, φ (x⁻¹ * z) * ker X.Γ ψ z y ∂X.μ := by sorry
