-- Prove2me | Theorems.Thm_GlobalTheory_BCT_DimFac_contractRight_map
-- name    : GlobalTheory.BCT.DimFac.contractRight_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:56:59.438838+00:00
-- url     : https://prove2.me/theorems/9f4fd697-4081-5224-a22c-9366160d4825
-- title:
--   Dim Fac: contract Right map
-- statement:
--   The Dim Fac construction uses the contract Right map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean#L75-L81

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

theorem GlobalTheory.BCT.DimFac.contractRight_map {W' M' : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup M'] [Module ℂ M']
    (l : Dual ℂ M') (A : W →ₗ[ℂ] W') (B : M →ₗ[ℂ] M') (t : W ⊗[ℂ] M) :
    contractRight l (TensorProduct.map A B t) = A (contractRight (l ∘ₗ B) t) := by sorry
