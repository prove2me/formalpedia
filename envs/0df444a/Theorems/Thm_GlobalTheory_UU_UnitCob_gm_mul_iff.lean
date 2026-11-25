-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitCob_gm_mul_iff
-- name    : GlobalTheory.UU.UnitCob.gm_mul_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:56:53.999557+00:00
-- url     : https://prove2.me/theorems/be0bf264-7013-52bd-a1fe-e40ce44fe965
-- title:
--   Unit Cob: gm mul iff
-- statement:
--   The Unit Cob construction uses the gm mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L126-L134

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

theorem GlobalTheory.UU.UnitCob.gm_mul_iff {Z W W' W'' : Scheme.{0}} (r₁ : Z ⟶ W) (r₂ : Z ⟶ W') (r₃ : Z ⟶ W'') (r₄ : Z ⟶ W'')
    (u : Γ(W, ⊤)ˣ) (v : Γ(W', ⊤)ˣ) (w : Γ(W'', ⊤)ˣ) :
    (∀ z, gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) ↔
      r₁.appTop.hom u.val * r₂.appTop.hom v.val = r₃.appTop.hom w.val * r₄.appTop.hom w.val := by sorry
