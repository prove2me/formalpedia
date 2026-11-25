-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_witData_of_isometry
-- name    : GlobalTheory.HostModel.witData_of_isometry
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:35.5622+00:00
-- url     : https://prove2.me/theorems/566c465b-9725-4e8d-abba-12614ec14290
-- title:
--   Host Model: wit Data of isometry
-- statement:
--   The Host Model construction uses the wit Data of isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L70-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)

theorem GlobalTheory.HostModel.witData_of_isometry (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E)
    (h : ∀ y : 𝓞 E, (arcIn c k bF).be (e y) (e y) = (arcIn c k bF).be y y) :
    WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF) (witIso c k bF) e := by sorry
