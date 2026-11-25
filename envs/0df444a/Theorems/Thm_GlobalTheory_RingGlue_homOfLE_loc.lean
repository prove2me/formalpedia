-- Prove2me | Theorems.Thm_GlobalTheory_RingGlue_homOfLE_loc
-- name    : GlobalTheory.RingGlue.homOfLE_loc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:45.843042+00:00
-- url     : https://prove2.me/theorems/3aa883ab-997a-4c99-9130-ca0c293fe383
-- title:
--   Ring Glue: hom Of LE loc
-- statement:
--   The Ring Glue construction uses the hom Of LE loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfRingMaps.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfRingMaps.lean#L20-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.RingGlue

theorem GlobalTheory.RingGlue.homOfLE_loc {Y B : Scheme.{0}} {W W' : Y.Opens} {V V' : B.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (ψ : Γ(B, V) ⟶ Γ(Y, W)) (ψ' : Γ(B, V') ⟶ Γ(Y, W'))
    (h : W' ≤ W) (e : V' ≤ V)
    (H : B.presheaf.map (homOfLE e).op ≫ ψ' = ψ ≫ Y.presheaf.map (homOfLE h).op) :
    Y.homOfLE h ≫ loc hV ψ = loc hV' ψ' := by sorry
