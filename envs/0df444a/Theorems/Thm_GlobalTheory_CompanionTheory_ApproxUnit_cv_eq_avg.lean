-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ApproxUnit_cv_eq_avg
-- name    : GlobalTheory.CompanionTheory.ApproxUnit.cv_eq_avg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:17:32.692718+00:00
-- url     : https://prove2.me/theorems/4e98a43b-3da3-423e-8466-05839633db7e
-- title:
--   Approx Unit: cv eq avg
-- statement:
--   The Approx Unit construction uses the cv eq avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CvAdjEqAvg.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CvAdjEqAvg.lean#L48-L54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CvAdjEqAvg
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
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ApproxUnit

theorem GlobalTheory.CompanionTheory.ApproxUnit.cv_eq_avg (X : Ctx) (φ ψ : X.G → ℂ) (hψ : IsBump X ψ) (g : X.G) :
    cv X.μ φ ψ g = ∫ w, φ (g * w) * ((‖ψ w⁻¹‖ : ℝ) : ℂ) ∂X.μ := by sorry
