-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_piTensor
-- name    : GlobalTheory.SmGL.UnitInd.isUnitarisable_piTensor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:44.933267+00:00
-- url     : https://prove2.me/theorems/e5a858c1-6cd9-4588-8499-65731f6b15f3
-- title:
--   Unit Ind: is Unitarisable pi Tensor
-- statement:
--   The Unit Ind construction uses the is Unitarisable pi Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L94-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L94-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem GlobalTheory.SmGL.UnitInd.isUnitarisable_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] {ρ : ∀ a, Representation ℂ (Γ a) (X a)}
    (h : ∀ a, IsUnitarisable (ρ a)) : IsUnitarisable (piTensor ρ) := by sorry
