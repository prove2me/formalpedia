-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_mem_of_sum
-- name    : GlobalTheory.CompanionTheory.FinHeis.Irred.mem_of_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:25.828023+00:00
-- url     : https://prove2.me/theorems/2d4d3820-76f6-4ada-b332-c0ab68ddc5b1
-- title:
--   Irred: mem of sum
-- statement:
--   The Irred construction uses the mem of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L38-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L38-L93

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

theorem GlobalTheory.CompanionTheory.FinHeis.Irred.mem_of_sum {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hd : SelfDual S Γ)
    (hs : IsSemi S al Γ) (hl : Law S al Γ φ) (N : Submodule ℂ M)
    (hN : ∀ x, ∀ v ∈ N, S.rho x v ∈ N) (s : Finset X) :
    ∀ a : X → ℂ, (∑ x ∈ s, a x • S.rho x φ) ∈ N → (∑ x ∈ s, a x • S.rho x φ) ≠ 0 → φ ∈ N := by sorry
