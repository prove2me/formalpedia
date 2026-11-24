-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ConvTest_support_cv_subset
-- name    : GlobalTheory.CompanionTheory.ConvTest.support_cv_subset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:55.893811+00:00
-- url     : https://prove2.me/theorems/23b59671-42cc-41f7-992f-98907ad390ff
-- title:
--   Conv Test: support cv subset
-- statement:
--   The Conv Test construction uses the support cv subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableReflect.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableReflect.lean#L14-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableReflect
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
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConvTest
variable (X : Ctx)

theorem GlobalTheory.CompanionTheory.ConvTest.support_cv_subset (φ ψ : X.G → ℂ) :
    Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ := by sorry
