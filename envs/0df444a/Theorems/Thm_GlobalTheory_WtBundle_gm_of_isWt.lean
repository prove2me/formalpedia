-- Prove2me | Theorems.Thm_GlobalTheory_WtBundle_gm_of_isWt
-- name    : GlobalTheory.WtBundle.gm_of_isWt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:01:24.045001+00:00
-- url     : https://prove2.me/theorems/a1030bf3-c91c-4de6-9cff-19879204ba76
-- title:
--   Wt Bundle: gm of is Wt
-- statement:
--   The Wt Bundle construction uses the gm of is Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L106-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
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
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem GlobalTheory.WtBundle.gm_of_isWt {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V)
    (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z V u := by sorry
