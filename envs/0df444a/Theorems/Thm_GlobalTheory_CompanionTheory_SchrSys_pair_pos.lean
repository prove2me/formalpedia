-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_pair_pos
-- name    : GlobalTheory.CompanionTheory.SchrSys.pair_pos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:06.390852+00:00
-- url     : https://prove2.me/theorems/34c06bdc-2682-48e5-9e96-f92e2fd1b20a
-- title:
--   Schr Sys: pair pos
-- statement:
--   The Schr Sys construction uses the pair pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L55-L77

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
variable {R : Type} [TopologicalSpace R] {κ : Type}

theorem GlobalTheory.CompanionTheory.SchrSys.pair_pos (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (hμ' : @Measure.IsOpenPosMeasure _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) : 0 < (pair μ φ φ).re := by sorry
