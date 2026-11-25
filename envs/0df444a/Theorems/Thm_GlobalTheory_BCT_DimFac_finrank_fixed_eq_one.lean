-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_finrank_fixed_eq_one
-- name    : GlobalTheory.BCT.DimFac.finrank_fixed_eq_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:37.688635+00:00
-- url     : https://prove2.me/theorems/c03dc895-38b0-48a0-93e2-77e013f4e4eb
-- title:
--   Dim Fac: finrank fixed eq one
-- statement:
--   The Dim Fac construction uses the finrank fixed eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L323-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L323-L372

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
variable {ι : Type} {e : ι → Γ →* Γ} {L : Subgroup Γ}

theorem GlobalTheory.BCT.DimFac.finrank_fixed_eq_one (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible)
    (h : ∀ i, HasComp ρ (e i) L 1) {m : V} (hm0 : m ≠ 0) (hm : m ∈ fixed ρ L) : finrank ℂ (fixed ρ L) = 1 := by sorry
