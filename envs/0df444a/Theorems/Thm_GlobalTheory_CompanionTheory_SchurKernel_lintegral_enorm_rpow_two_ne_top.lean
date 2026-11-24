-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchurKernel_lintegral_enorm_rpow_two_ne_top
-- name    : GlobalTheory.CompanionTheory.SchurKernel.lintegral_enorm_rpow_two_ne_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:23.257805+00:00
-- url     : https://prove2.me/theorems/6e6df88a-aa8c-4953-8713-d7a35e118882
-- title:
--   Schur Kernel: lintegral enorm rpow two ne top
-- statement:
--   The Schur Kernel construction uses the lintegral enorm rpow two ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralEnormRpowTwoNeTop.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralEnormRpowTwoNeTop.lean#L10-L14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralEnormRpowTwoNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchurKernel

theorem GlobalTheory.CompanionTheory.SchurKernel.lintegral_enorm_rpow_two_ne_top {α : Type} [MeasurableSpace α] {ν : Measure α} {g : α → ℂ}
    (hg : MemLp g 2 ν) : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := by sorry
