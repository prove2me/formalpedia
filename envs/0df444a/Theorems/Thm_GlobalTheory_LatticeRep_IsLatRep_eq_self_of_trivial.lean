-- Prove2me | Theorems.Thm_GlobalTheory_LatticeRep_IsLatRep_eq_self_of_trivial
-- name    : GlobalTheory.LatticeRep.IsLatRep.eq_self_of_trivial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:02.505836+00:00
-- url     : https://prove2.me/theorems/bb7a928d-6a52-4a06-876f-f36691dc0f52
-- title:
--   Is Lat Rep: eq self of trivial
-- statement:
--   The Is Lat Rep construction uses the eq self of trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSelfOfTrivial.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSelfOfTrivial.lean#L97-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeRep
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}

theorem GlobalTheory.LatticeRep.IsLatRep.eq_self_of_trivial (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) {g : Γ}
    (hg : ∀ x, ρ g x = x) (m : M) : Om g m = m := by sorry
