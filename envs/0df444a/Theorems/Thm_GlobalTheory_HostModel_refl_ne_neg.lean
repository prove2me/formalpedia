-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_refl_ne_neg
-- name    : GlobalTheory.HostModel.refl_ne_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:07.037106+00:00
-- url     : https://prove2.me/theorems/cecfc5b6-7b69-4095-94fe-bdf5b5252c69
-- title:
--   Host Model: refl ne neg
-- statement:
--   The Host Model construction uses the refl ne neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L89-L91

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
omit [IsCMField E]

theorem GlobalTheory.HostModel.refl_ne_neg : LinearEquiv.refl (𝓞 E) (𝓞 E) ≠ (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) := by sorry
