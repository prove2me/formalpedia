-- Prove2me | Theorems.Thm_GlobalTheory_exists_splitTorus_points_mulEquiv
-- name    : GlobalTheory.exists_splitTorus_points_mulEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:08.188151+00:00
-- url     : https://prove2.me/theorems/885632fa-9a63-4f8f-84ba-b22af8e25f34
-- title:
--   Global Theory: exists split Torus points mul Equiv
-- statement:
--   The Global Theory construction uses the exists split Torus points mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L146-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_splitTorus_points_mulEquiv :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val := by sorry
