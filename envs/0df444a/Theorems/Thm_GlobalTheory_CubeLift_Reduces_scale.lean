-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_Reduces_scale
-- name    : GlobalTheory.CubeLift.Reduces.scale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:14:27.55655+00:00
-- url     : https://prove2.me/theorems/f68cab93-a7df-47e4-9a2c-87e3ed8cd339
-- title:
--   Reduces: scale
-- statement:
--   The Reduces construction uses the scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L255-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L255-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}

theorem GlobalTheory.CubeLift.Reduces.scale {t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1])}
    {σ₀ : CubTriv P₀.c i₀} (h : Reduces w t σ₀) {g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ}
    (hg : app (bcMap (red J) X) g = 1) : Reduces w (scaleGen g t) σ₀ := by sorry
