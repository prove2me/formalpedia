-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahoriFactorization_of_elim
-- name    : GroundTheory.Automorphic.Parabolic.iwahoriFactorization_of_elim
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:33.564853+00:00
-- url     : https://prove2.me/theorems/6473c441-0441-4011-94ba-ccd6cb9bbbcd
-- title:
--   Parabolic: iwahori Factorization of elim
-- statement:
--   The Parabolic construction uses the iwahori Factorization of elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L165-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L165-L199

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}

theorem GroundTheory.Automorphic.Parabolic.iwahoriFactorization_of_elim (K : Subgroup (GL (Fin n) F))
    (hdiag : ∀ h ∈ K, ∀ a, (h : GL (Fin n) F) a a ≠ 0)
    (helim : ∀ h ∈ K, ∀ a, elimGL β ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a ∈ K)
    (hlevi : ∀ p (hp : p ∈ blockUpper F n β), p ∈ K →
      ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ K)
    (hlevi' : ∀ p (hp : p ∈ blockUpper F n (OrderDual.toDual ∘ β)), p ∈ K →
      ((leviProj F n (OrderDual.toDual ∘ β) ⟨p, hp⟩ : levi F n (OrderDual.toDual ∘ β)) :
        GL (Fin n) F) ∈ K) :
    ∀ k ∈ K, ∃ z ∈ K ⊓ oppositeUnipotentRadical F n β, ∃ y ∈ K ⊓ levi F n β,
      ∃ x ∈ K ⊓ unipotentRadical F n β, k = z * y * x := by sorry
