-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrSys_pair_conj
-- name    : GlobalTheory.CompanionTheory.SchrSys.pair_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:11:59.661128+00:00
-- url     : https://prove2.me/theorems/b49fa43d-fd66-4711-9b99-7a3a78104e27
-- title:
--   Schr Sys: pair conj
-- statement:
--   The Schr Sys construction uses the pair conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IntegrablePair.lean#L46-L53

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

theorem GlobalTheory.CompanionTheory.SchrSys.pair_conj (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by sorry
