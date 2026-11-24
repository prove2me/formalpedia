-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_continuous_ker
-- name    : GlobalTheory.CompanionTheory.KernelBasic.continuous_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:01.244892+00:00
-- url     : https://prove2.me/theorems/f90a6c9a-5ff5-4552-9c18-354ae8270f1b
-- title:
--   Kernel Basic: continuous ker
-- statement:
--   The Kernel Basic construction uses the continuous ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L30-L45

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

theorem GlobalTheory.CompanionTheory.KernelBasic.continuous_ker (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) :
    Continuous (Function.uncurry (ker X.Γ φ)) := by sorry
