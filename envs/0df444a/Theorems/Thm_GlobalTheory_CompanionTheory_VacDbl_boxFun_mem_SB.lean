-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacDbl_boxFun_mem_SB
-- name    : GlobalTheory.CompanionTheory.VacDbl.boxFun_mem_SB
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:06.174208+00:00
-- url     : https://prove2.me/theorems/4fb89b12-cdc2-4132-8d38-1bc02b182b89
-- title:
--   Vac Dbl: box Fun mem SB
-- statement:
--   The Vac Dbl construction uses the box Fun mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoxFunMemSB.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoxFunMemSB.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoxFunMemSB
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacDbl

theorem GlobalTheory.CompanionTheory.VacDbl.boxFun_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by sorry
