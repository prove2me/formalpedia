-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrModel_isModel_sys
-- name    : GlobalTheory.CompanionTheory.SchrModel.isModel_sys
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:47.377685+00:00
-- url     : https://prove2.me/theorems/cd17fa5d-fbc2-4de9-a0bc-7eabed1c290c
-- title:
--   Schr Model: is Model sys
-- statement:
--   The Schr Model construction uses the is Model sys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LocallyCompactOfGoodChar.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/LocallyCompactOfGoodChar.lean#L143-L147

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

theorem GlobalTheory.CompanionTheory.SchrModel.isModel_sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    IsModel ψ d μ (sys h d μ hμ) := by sorry
