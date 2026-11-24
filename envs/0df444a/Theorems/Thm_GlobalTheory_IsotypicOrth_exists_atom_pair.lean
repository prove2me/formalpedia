-- Prove2me | Theorems.Thm_GlobalTheory_IsotypicOrth_exists_atom_pair
-- name    : GlobalTheory.IsotypicOrth.exists_atom_pair
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:03.512353+00:00
-- url     : https://prove2.me/theorems/70949bb1-9758-4c94-bbfa-1214eef83823
-- title:
--   Isotypic Orth: exists atom pair
-- statement:
--   The Isotypic Orth construction uses the exists atom pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypes.lean#L152-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypes.lean#L152-L165

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

theorem GlobalTheory.IsotypicOrth.exists_atom_pair
    (hsum : ∀ X : Subrepresentation ρ,
      X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (Y : Subrepresentation ρ) (ψ : V)
    (h : ∃ y ∈ Y.toSubmodule, B y ψ ≠ 0) :
    ∃ S₁ : Subrepresentation ρ, IsAtom S₁ ∧ S₁ ≤ Y ∧ ∃ x ∈ S₁.toSubmodule, B x ψ ≠ 0 := by sorry
