-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitCob_cocycle_of_points
-- name    : GlobalTheory.UU.UnitCob.cocycle_of_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:30.187515+00:00
-- url     : https://prove2.me/theorems/416f8ba1-d062-56c9-9aad-f80f1edf02ef
-- title:
--   Unit Cob: cocycle of points
-- statement:
--   The Unit Cob construction uses the cocycle of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L143-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L143-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitCob
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

theorem GlobalTheory.UU.UnitCob.cocycle_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over S) (t t' t'' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev₂ (t * t') t'' y φ * ev₂ t t' y φ = ev₂ t (t' * t'') y φ * ev₂ t' t'' y φ) :
    AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) φ =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) φ := by sorry
