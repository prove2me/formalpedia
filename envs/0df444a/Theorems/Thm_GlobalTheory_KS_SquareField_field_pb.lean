-- Prove2me | Theorems.Thm_GlobalTheory_KS_SquareField_field_pb
-- name    : GlobalTheory.KS.SquareField.field_pb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:41.639467+00:00
-- url     : https://prove2.me/theorems/524a4cfc-6ad3-416e-a43f-ada7b6ede5ec
-- title:
--   Square Field: field pb
-- statement:
--   The Square Field construction uses the field pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsLieCombZero.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsLieCombZero.lean#L78-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsLieCombZero
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.SquareField
variable {K : Type} [Field K]
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}

theorem GlobalTheory.KS.SquareField.field_pb {v : epsR K ⟶ A₀} {dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)}
    (hv : IsTangent v) (hd : IsInvDer v dd) (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = v)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = pbT f.left (dd W h) O := by sorry
