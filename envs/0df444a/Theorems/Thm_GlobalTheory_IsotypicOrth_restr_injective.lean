-- Prove2me | Theorems.Thm_GlobalTheory_IsotypicOrth_restr_injective
-- name    : GlobalTheory.IsotypicOrth.restr_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:05.863801+00:00
-- url     : https://prove2.me/theorems/709342b7-d1a2-4edb-969d-8485e279f804
-- title:
--   Isotypic Orth: restr injective
-- statement:
--   The Isotypic Orth construction uses the restr injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypes.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypes.lean#L78-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsComplOrthogonalOfNoCommonIrreducibleTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.IsotypicOrth
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}

theorem GlobalTheory.IsotypicOrth.restr_injective (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule) := by sorry
