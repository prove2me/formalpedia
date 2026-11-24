-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_c_ne
-- name    : GlobalTheory.CompanionTheory.FinHeis.Irred.c_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:23.4759+00:00
-- url     : https://prove2.me/theorems/6fe616f7-a50a-42df-8441-b390ec91f4ea
-- title:
--   Irred: c ne
-- statement:
--   The Irred construction uses the c ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L12-L16

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

theorem GlobalTheory.CompanionTheory.FinHeis.Irred.c_ne (x y : X) : S.c x y ≠ 0 := by sorry
