-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_irreducible
-- name    : GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:18.712082+00:00
-- url     : https://prove2.me/theorems/942bee25-fb57-40dd-a13f-e25f4de67798
-- title:
--   Irred: irreducible
-- statement:
--   The Irred construction uses the irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L95-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean#L95-L136

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

theorem GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible : ∀ {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
    (al : X → ℂ) (Γ : AddSubgroup X) (φ : M), SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ →
    Cyclic S φ →
    (∀ N : Submodule ℂ M, (∀ x, ∀ v ∈ N, S.rho x v ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ v : M, v ≠ 0 → Cyclic S v := by sorry
