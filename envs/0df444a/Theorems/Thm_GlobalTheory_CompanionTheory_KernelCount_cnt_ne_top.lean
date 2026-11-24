-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_cnt_ne_top
-- name    : GlobalTheory.CompanionTheory.KernelCount.cnt_ne_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:32.847175+00:00
-- url     : https://prove2.me/theorems/b35cff05-6040-45d1-9841-25d2ba5a7964
-- title:
--   Kernel Count: cnt ne top
-- statement:
--   The Kernel Count construction uses the cnt ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CntBasicOfKerBasic.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CntBasicOfKerBasic.lean#L12-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CntBasicOfKerBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelCount

theorem GlobalTheory.CompanionTheory.KernelCount.cnt_ne_top (X : Ctx) (Ω : Set X.G) (hΩ : IsCompact Ω) (x : X.G) : cnt X.Γ Ω x ≠ ⊤ := by sorry
