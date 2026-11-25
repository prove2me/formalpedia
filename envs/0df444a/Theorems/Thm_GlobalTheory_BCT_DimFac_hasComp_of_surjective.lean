-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_hasComp_of_surjective
-- name    : GlobalTheory.BCT.DimFac.hasComp_of_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:46.646956+00:00
-- url     : https://prove2.me/theorems/2bd53797-16d0-559b-92ad-f8bb9e6e4f5a
-- title:
--   Dim Fac: has Comp of surjective
-- statement:
--   The Dim Fac construction uses the has Comp of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L244-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L244-L262

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

theorem GlobalTheory.BCT.DimFac.hasComp_of_surjective {H : Type} [Group H] (ρ : Representation ℂ Γ V) (e : Γ →* Γ) (L : Subgroup Γ)
    (q : Γ →* H) (hq : Function.Surjective q) (hqe : ∀ g, q (e g) = q g) (σ : Representation ℂ H W)
    (hσ : σ.IsIrreducible) (U : Subgroup H) (hU : fixed σ U ≠ ⊥) [FiniteDimensional ℂ (fixed σ U)]
    (f : W →ₗ[ℂ] V) (hf0 : f ≠ 0) (hf : ∀ g x, f (σ (q g) x) = ρ (e g) (f x)) (K : Subgroup H)
    (h1 : ∀ g ∈ L, q g ∈ K) (h2 : ∀ k ∈ K, ∃ g ∈ L, q g = k) : HasComp ρ e L (finrank ℂ (fixed σ K)) := by sorry
