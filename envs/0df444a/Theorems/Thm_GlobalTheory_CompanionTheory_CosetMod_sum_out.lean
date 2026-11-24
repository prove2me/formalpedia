-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CosetMod_sum_out
-- name    : GlobalTheory.CompanionTheory.CosetMod.sum_out
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:48.030248+00:00
-- url     : https://prove2.me/theorems/6451c402-9656-4ade-bba1-98fd4bf6fe06
-- title:
--   Coset Mod: sum out
-- statement:
--   The Coset Mod construction uses the sum out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SchrodingerModelSelfDualLattice.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SchrodingerModelSelfDualLattice.lean#L8-L33

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetMod

theorem GlobalTheory.CompanionTheory.CosetMod.sum_out {G : Type} [AddCommGroup G] (H : AddSubgroup G) [Fintype (G ⧸ H)] (χ : AddChar G ℂ)
    (hχ : ∀ h ∈ H, χ h = 1) :
    ((∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = Fintype.card (G ⧸ H)) ∧
      (¬ (∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = 0) := by sorry
