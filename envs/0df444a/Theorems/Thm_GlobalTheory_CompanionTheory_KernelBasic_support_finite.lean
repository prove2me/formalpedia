-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_support_finite
-- name    : GlobalTheory.CompanionTheory.KernelBasic.support_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:08.156357+00:00
-- url     : https://prove2.me/theorems/de265e16-a254-42b6-a992-4cfba55c337f
-- title:
--   Kernel Basic: support finite
-- statement:
--   The Kernel Basic construction uses the support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L23-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelBasic

theorem GlobalTheory.CompanionTheory.KernelBasic.support_finite (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite := by sorry
