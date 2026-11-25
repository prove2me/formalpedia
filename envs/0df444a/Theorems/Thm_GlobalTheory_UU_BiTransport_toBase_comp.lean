-- Prove2me | Theorems.Thm_GlobalTheory_UU_BiTransport_toBase_comp
-- name    : GlobalTheory.UU.BiTransport.toBase_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:16.457966+00:00
-- url     : https://prove2.me/theorems/f19f1315-e083-50d2-81d6-58cf69c1c828
-- title:
--   Bi Transport: to Base comp
-- statement:
--   The Bi Transport construction uses the to Base comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L61-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}
omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj G₀] [IsCommMonObj G₀] [GrpObj H₀]

theorem GlobalTheory.UU.BiTransport.toBase_comp (hE : E ≫ H.hom = H₀.hom ≫ ρ) (hi : E ≫ i.left = i₀.left ≫ F) {T : Over S₀} (t : T ⟶ H₀) :
    toBase hE t ≫ i = toBase hw (t ≫ i₀) := by sorry
