-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_exists_coord
-- name    : GlobalTheory.EquivDesc.exists_coord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:41.970932+00:00
-- url     : https://prove2.me/theorems/f29119f0-054b-4b83-b989-3da5d0868560
-- title:
--   Equiv Desc: exists coord
-- statement:
--   The Equiv Desc construction uses the exists coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L70-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}

theorem GlobalTheory.EquivDesc.exists_coord {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (U : G.left.Opens)
    (u : Multiplicative X →* Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) :
    ∃ τ : opn U ⟶ splitTorus S X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g g' : Z ⟶ opn U),
      g' ≫ opnι U = (t ≫ i) * (g ≫ opnι U) → g' ≫ τ = t * (g ≫ τ) := by sorry
