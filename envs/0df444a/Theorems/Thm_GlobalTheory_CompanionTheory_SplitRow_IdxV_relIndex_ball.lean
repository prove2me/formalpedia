-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_ball
-- name    : GlobalTheory.CompanionTheory.SplitRow.IdxV.relIndex_ball
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:13.962785+00:00
-- url     : https://prove2.me/theorems/534465e1-4c19-488c-8ab3-e366f72884ff
-- title:
--   Idx V: rel Index ball
-- statement:
--   The Idx V construction uses the rel Index ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L37-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L37-L78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.SplitRow.IdxV.relIndex_ball (ϖ : kˣ) (hϖ : ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ) (b : ℤ) :
    (ball (1 : k)).relIndex (ball ((ϖ ^ b : kˣ) : k)) = resCard k ^ b.toNat := by sorry
