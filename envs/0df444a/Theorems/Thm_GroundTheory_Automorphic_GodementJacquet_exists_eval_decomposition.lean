-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_exists_eval_decomposition
-- name    : GroundTheory.Automorphic.GodementJacquet.exists_eval_decomposition
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:27.306525+00:00
-- url     : https://prove2.me/theorems/dd4fab1f-4a30-4596-8597-cd0db9043d82
-- title:
--   Godement Jacquet: exists eval decomposition
-- statement:
--   The Godement Jacquet construction uses the exists eval decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJInducedCoeff.lean#L81-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJInducedCoeff.lean#L81-L155

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.GodementJacquet.exists_eval_decomposition (hσ : IsSmooth σ) {m : ℕ} {R : Finset (GL (Fin n) F)}
    (hR₀ : ∀ x ∈ R, x ∈ integralGL F n)
    (hR : ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m)
    (lam : Module.Dual ℂ (parabolicIndSpace F n β σ)) :
    ∃ ℓ : GL (Fin n) F → Module.Dual ℂ W,
      (∀ x, ℓ x ∈ fixedVectors (Representation.dual σ)
        ((congruenceSubgroup F n m).subgroupOf (levi F n β))) ∧
      ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
        lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) := by sorry
