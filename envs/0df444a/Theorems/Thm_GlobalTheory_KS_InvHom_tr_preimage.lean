-- Prove2me | Theorems.Thm_GlobalTheory_KS_InvHom_tr_preimage
-- name    : GlobalTheory.KS.InvHom.tr_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:56.51248+00:00
-- url     : https://prove2.me/theorems/bd689402-512b-4106-a1b9-cc4e04ced544
-- title:
--   Inv Hom: tr preimage
-- statement:
--   The Inv Hom construction uses the tr preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L68-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvHom
variable {K : Type} [Field K]
variable {A : Over (Sp K)} [GrpObj A]

theorem GlobalTheory.KS.InvHom.tr_preimage {v : epsR K ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    (tr v).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by sorry
