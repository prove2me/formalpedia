-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_extTensor
-- name    : GlobalTheory.SmGL.UnitInd.isUnitarisable_extTensor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:43.968185+00:00
-- url     : https://prove2.me/theorems/f3bb63da-0fb3-4167-98ec-8742e30799aa
-- title:
--   Unit Ind: is Unitarisable ext Tensor
-- statement:
--   The Unit Ind construction uses the is Unitarisable ext Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L38-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L38-L60

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

theorem GlobalTheory.SmGL.UnitInd.isUnitarisable_extTensor {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (h₁ : IsUnitarisable ρ) (h₂ : IsUnitarisable σ) : IsUnitarisable (extTensor ρ σ) := by sorry
