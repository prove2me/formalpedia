-- Prove2me | Theorems.Thm_GlobalTheory_KS_InvHom_invDer_along_hom
-- name    : GlobalTheory.KS.InvHom.invDer_along_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:58.841513+00:00
-- url     : https://prove2.me/theorems/ce108fea-93e1-4e66-8d62-82a79a7dd513
-- title:
--   Inv Hom: inv Der along hom
-- statement:
--   The Inv Hom construction uses the inv Der along hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsAlongGroupHom.lean#L184-L189

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

theorem GlobalTheory.KS.InvHom.invDer_along_hom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by sorry
