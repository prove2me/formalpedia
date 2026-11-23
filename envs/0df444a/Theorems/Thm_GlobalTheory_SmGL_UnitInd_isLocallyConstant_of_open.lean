-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnitInd_isLocallyConstant_of_open
-- name    : GlobalTheory.SmGL.UnitInd.isLocallyConstant_of_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:08.533693+00:00
-- url     : https://prove2.me/theorems/47642439-2997-49fe-9c62-f4ba02730694
-- title:
--   Unit Ind: is Locally Constant of open
-- statement:
--   The Unit Ind construction uses the is Locally Constant of open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L205-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L205-L210

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

theorem GlobalTheory.SmGL.UnitInd.isLocallyConstant_of_open {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → Y}
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (h : ∀ x, ∀ u ∈ U, f (x * u) = f x) : IsLocallyConstant f := by sorry
