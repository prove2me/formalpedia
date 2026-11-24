-- Prove2me | Theorems.Thm_GlobalTheory_KS_InvHom_pull
-- name    : GlobalTheory.KS.InvHom.pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:39:52.526183+00:00
-- url     : https://prove2.me/theorems/22143f4a-74ac-42bb-8f8a-952725d341d9
-- title:
--   Inv Hom: pull
-- statement:
--   The Inv Hom construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L77-L88

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

theorem GlobalTheory.KS.InvHom.pull {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) {Z : Over (Sp K)}
    (S : Z ⟶ epsR K ⊗ A) (W : A.left.Opens) (f : Γ(A.left, W)) (O : Z.left.Opens)
    (hO : O ≤ (S ≫ snd (epsR K) A).left ⁻¹ᵁ W) :
    pbT (S ≫ tr v).left f O = pbT (S ≫ snd (epsR K) A).left f O +
      constFn (R := DualNumber K) (S ≫ fst (epsR K) A).left O DualNumber.eps *
        pbT (S ≫ snd (epsR K) A).left (dd W f) O := by sorry
