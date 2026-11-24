-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelCount_cnt_mono
-- name    : GlobalTheory.CompanionTheory.KernelCount.cnt_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:51.606734+00:00
-- url     : https://prove2.me/theorems/cd6c2414-c012-4e1f-a9a4-4c829246c1bb
-- title:
--   Kernel Count: cnt mono
-- statement:
--   The Kernel Count construction uses the cnt mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CntBasicOfKerBasic.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CntBasicOfKerBasic.lean#L44-L46

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

theorem GlobalTheory.CompanionTheory.KernelCount.cnt_mono (X : Ctx) {Ω Ω' : Set X.G} (h : Ω ⊆ Ω') (x : X.G) :
    cnt X.Γ Ω x ≤ cnt X.Γ Ω' x := by sorry
