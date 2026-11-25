-- Prove2me | Theorems.Thm_GlobalTheory_WtBundle_exists_bundle
-- name    : GlobalTheory.WtBundle.exists_bundle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:22.091951+00:00
-- url     : https://prove2.me/theorems/932d138d-e6bf-4b5f-b96e-626e34a6bb11
-- title:
--   Wt Bundle: exists bundle
-- statement:
--   The Wt Bundle construction uses the exists bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L149-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CommGroupCommonFactorQuotientCancel.lean#L149-L195

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
variable (Q : TQ G X)

theorem GlobalTheory.WtBundle.exists_bundle (χ : X) : ∃ (N : LB Q.B.left) (u : ∀ j, Γ(G.left, Q.q.left ⁻¹ᵁ N.U j)ˣ), N.IsLB ∧
    (∀ j, IsWt Q.i _ (u j).val χ) ∧
    ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z) (i j : N.ι), Q.q.left (g z) ∈ N.U i → Q.q.left (g z) ∈ N.U j →
      gm g z (Q.q.left ⁻¹ᵁ N.U i) (u i) =
        gm (g ≫ Q.q.left) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (Q.q.left ⁻¹ᵁ N.U j) (u j) := by sorry
