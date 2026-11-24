-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_c_swap
-- name    : GlobalTheory.CompanionTheory.FinHeis.Irred.c_swap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:22.065799+00:00
-- url     : https://prove2.me/theorems/1bc7391a-8e58-4576-b3a3-ca4ebdb870c9
-- title:
--   Irred: c swap
-- statement:
--   The Irred construction uses the c swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)

theorem GlobalTheory.CompanionTheory.FinHeis.Irred.c_swap (x y : X) : S.c x y * S.c y x = 1 := by sorry
