-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_central_contracting
-- name    : GroundTheory.Automorphic.Parabolic.exists_central_contracting
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:14.111309+00:00
-- url     : https://prove2.me/theorems/54718c88-34f2-52bf-afcc-9ebf6640e492
-- title:
--   Parabolic: exists central contracting
-- statement:
--   The Parabolic construction uses the exists central contracting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L486-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L486-L511

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
variable (β)

theorem GroundTheory.Automorphic.Parabolic.exists_central_contracting (m : ℕ) :
    ∃ a ∈ levi F n β, (∀ y ∈ levi F n β, a * y = y * a) ∧
      (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β,
        a * u * a⁻¹ ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β) ∧
      (∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
        a⁻¹ * z * a ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) ∧
      ∀ U ∈ 𝓝 (1 : GL (Fin n) F), ∃ k : ℕ,
        (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, a ^ k * u * (a ^ k)⁻¹ ∈ U) ∧
        ∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
          (a ^ k)⁻¹ * z * a ^ k ∈ U := by sorry
