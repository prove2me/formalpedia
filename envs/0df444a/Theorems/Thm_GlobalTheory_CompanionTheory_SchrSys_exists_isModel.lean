-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_exists_isModel
-- name    : GlobalTheory.CompanionTheory.SchrSys.exists_isModel
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:13.447094+00:00
-- url     : https://prove2.me/theorems/12816926-e7c2-4e74-a6fc-fea12caedfa9
-- title:
--   Schr Sys: exists is Model
-- statement:
--   The Schr Sys construction uses the exists is Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L81-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L81-L120

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrSys

theorem GlobalTheory.CompanionTheory.SchrSys.exists_isModel : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) , GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ S : Sys W (SB (κ → R)), IsModel ψ d μ S := by sorry
