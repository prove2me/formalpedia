-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdxAd_sgl_ne
-- name    : GlobalTheory.CompanionTheory.IdxAd.sgl_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:12.810832+00:00
-- url     : https://prove2.me/theorems/12860df0-3081-460b-8fb4-3050aa8f8ac3
-- title:
--   Idx Ad: sgl ne
-- statement:
--   The Idx Ad construction uses the sgl ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L26-L28

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
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.IdxAd.sgl_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) : sgl v x w = 0 := by sorry
