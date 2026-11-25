-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrModel_exists_isModel
-- name    : GlobalTheory.CompanionTheory.SchrModel.exists_isModel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:21.051796+00:00
-- url     : https://prove2.me/theorems/6a4eeecf-4b19-50f0-89cc-f0cd1456656b
-- title:
--   Schr Model: exists is Model
-- statement:
--   The Schr Model construction uses the exists is Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LocallyCompactOfGoodChar.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LocallyCompactOfGoodChar.lean#L149-L152

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LocallyCompactOfGoodChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.SchrLaw
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrModel
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

theorem GlobalTheory.CompanionTheory.SchrModel.exists_isModel {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)), IsModel ψ d μ S := by sorry
