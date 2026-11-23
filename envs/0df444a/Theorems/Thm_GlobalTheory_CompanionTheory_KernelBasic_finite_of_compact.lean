-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_finite_of_compact
-- name    : GlobalTheory.CompanionTheory.KernelBasic.finite_of_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:01.191965+00:00
-- url     : https://prove2.me/theorems/81fd5c61-3ed7-474d-a688-96977c76ab7b
-- title:
--   Kernel Basic: finite of compact
-- statement:
--   The Kernel Basic construction uses the finite of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteOfCompact.lean#L11-L21

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

theorem GlobalTheory.CompanionTheory.KernelBasic.finite_of_compact (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) {U V : Set X.G}
    (hU : IsCompact U) (hV : IsCompact V) :
    {γ : X.Γ | ∃ x ∈ U, ∃ y ∈ V, φ (x⁻¹ * (γ : X.G) * y) ≠ 0}.Finite := by sorry
