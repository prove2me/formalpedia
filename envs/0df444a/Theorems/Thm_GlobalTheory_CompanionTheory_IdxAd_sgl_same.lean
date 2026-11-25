-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdxAd_sgl_same
-- name    : GlobalTheory.CompanionTheory.IdxAd.sgl_same
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:47.044644+00:00
-- url     : https://prove2.me/theorems/cb0c64f7-8fb3-5a81-8752-8dde8996db7e
-- title:
--   Idx Ad: sgl same
-- statement:
--   The Idx Ad construction uses the sgl same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SwapCApply.lean#L22-L24

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

theorem GlobalTheory.CompanionTheory.IdxAd.sgl_same (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : sgl v x v = x := by sorry
