-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerPoint_support_cv_adj_cv
-- name    : GlobalTheory.CompanionTheory.KerPoint.support_cv_adj_cv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:38.638721+00:00
-- url     : https://prove2.me/theorems/c053454c-e736-4441-bbd9-dbb724ea47ab
-- title:
--   Ker Point: support cv adj cv
-- statement:
--   The Ker Point construction uses the support cv adj cv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqZeroOfLeSmall.lean#L11-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfLeSmall
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerPoint

theorem GlobalTheory.CompanionTheory.KerPoint.support_cv_adj_cv (hKB : KerBasic) (hCv : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ)
    (N : Set X.G) (hNc : IsCompact N) (hN : tsupport ψ ⊆ N) :
    Function.support (cv X.μ (adj ψ) (cv X.μ φ ψ)) ⊆ N⁻¹ * (tsupport φ * N) := by sorry
