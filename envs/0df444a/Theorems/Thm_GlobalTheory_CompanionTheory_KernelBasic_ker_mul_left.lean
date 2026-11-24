-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_ker_mul_left
-- name    : GlobalTheory.CompanionTheory.KernelBasic.ker_mul_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:38.435291+00:00
-- url     : https://prove2.me/theorems/004af9d8-091b-4491-8500-b469a4adb2f4
-- title:
--   Kernel Basic: ker mul left
-- statement:
--   The Kernel Basic construction uses the ker mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L47-L54

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

theorem GlobalTheory.CompanionTheory.KernelBasic.ker_mul_left (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ (γ * x) y = ker X.Γ φ x y := by sorry
