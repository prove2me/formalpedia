-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_eigen
-- name    : GlobalTheory.CompanionTheory.FinHeis.Irred.eigen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:18.923333+00:00
-- url     : https://prove2.me/theorems/e2bb2eec-4254-434b-9248-221c4e06a063
-- title:
--   Irred: eigen
-- statement:
--   The Irred construction uses the eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L29-L36

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

theorem GlobalTheory.CompanionTheory.FinHeis.Irred.eigen {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hs : IsSemi S al Γ) (hl : Law S al Γ φ)
    {γ : X} (hγ : γ ∈ Γ) (x : X) :
    al γ • S.rho γ (S.rho x φ) = S.c γ x ^ 2 • S.rho x φ := by sorry
