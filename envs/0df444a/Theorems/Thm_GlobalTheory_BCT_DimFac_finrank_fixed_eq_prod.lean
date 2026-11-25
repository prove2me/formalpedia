-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_finrank_fixed_eq_prod
-- name    : GlobalTheory.BCT.DimFac.finrank_fixed_eq_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:48.672515+00:00
-- url     : https://prove2.me/theorems/8acee847-d42e-423d-b67b-2f99f47ecc2d
-- title:
--   Dim Fac: finrank fixed eq prod
-- statement:
--   The Dim Fac construction uses the finrank fixed eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L374-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L374-L417

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

theorem GlobalTheory.BCT.DimFac.finrank_fixed_eq_prod (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) (T : Finset ι) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V), ρ.IsIrreducible → ∀ d : ι → ℕ,
      (∀ i, HasComp ρ (e i) L (d i)) → (∀ i ∉ T, d i = 1) →
      (∃ m : V, m ≠ 0 ∧ ∀ g ∈ L, (∀ i ∈ T, e i g = 1) → ρ g m = m) → finrank ℂ (fixed ρ L) = ∏ i ∈ T, d i := by sorry
