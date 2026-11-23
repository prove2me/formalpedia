-- Prove2me | Theorems.Thm_GlobalTheory_KS_InvHom_thick
-- name    : GlobalTheory.KS.InvHom.thick
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:02.426303+00:00
-- url     : https://prove2.me/theorems/178c95b2-7254-42c0-998f-44ae9c8872d3
-- title:
--   Inv Hom: thick
-- statement:
--   The Inv Hom construction uses the thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L49-L61

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

theorem GlobalTheory.KS.InvHom.thick (A : Over (Sp K)) :
    (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((jA A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)),
      ∃! ab : Γ(A.left, O) × Γ(A.left, O), F = ((snd (epsR K) A).left.app O).hom ab.1 +
        constFn (R := DualNumber K) (fst (epsR K) A).left _ DualNumber.eps *
          ((snd (epsR K) A).left.app O).hom ab.2 := by sorry
