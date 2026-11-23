-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SplitRow_IdxV_mem_ball
-- name    : GlobalTheory.CompanionTheory.SplitRow.IdxV.mem_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:39.5843+00:00
-- url     : https://prove2.me/theorems/f983f668-88a0-4aaf-b1e2-bdb112b2661a
-- title:
--   Idx V: mem ball
-- statement:
--   The Idx V construction uses the mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L35-L35

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.SplitRow.IdxV.mem_ball (c x : k) : x ∈ ball c ↔ x * c ∈ 𝒪[k] := by sorry
