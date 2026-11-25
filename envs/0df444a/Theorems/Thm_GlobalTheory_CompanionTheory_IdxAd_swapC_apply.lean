-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdxAd_swapC_apply
-- name    : GlobalTheory.CompanionTheory.IdxAd.swapC_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:27.282693+00:00
-- url     : https://prove2.me/theorems/c870e93b-7610-47d2-a2c9-49b567c92331
-- title:
--   Idx Ad: swap C apply
-- statement:
--   The Idx Ad construction uses the swap C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L34-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsLatticeOfCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SwapCApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdxAd

theorem GlobalTheory.CompanionTheory.IdxAd.swapC_apply {k : Type} [CommRing k] (z : k × k) : swapC k z = z.swap := by sorry
