-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_schur_of_fixed
-- name    : GlobalTheory.BCT.DimFac.schur_of_fixed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:39.92585+00:00
-- url     : https://prove2.me/theorems/808c703b-4600-4cdf-ab6c-0a31c6b14a35
-- title:
--   Dim Fac: schur of fixed
-- statement:
--   The Dim Fac construction uses the schur of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L22-L38

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

theorem GlobalTheory.BCT.DimFac.schur_of_fixed {σ : Representation ℂ Γ W} (hσ : σ.IsIrreducible) (U : Subgroup Γ) (h0 : fixed σ U ≠ ⊥)
    [FiniteDimensional ℂ (fixed σ U)] (T : End ℂ W) (hT : ∀ g, T * σ g = σ g * T) : ∃ c : ℂ, T = c • 1 := by sorry
