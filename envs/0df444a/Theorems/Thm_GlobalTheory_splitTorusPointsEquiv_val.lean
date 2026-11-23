-- Prove2me | Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
-- name    : GlobalTheory.splitTorusPointsEquiv_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:12.80951+00:00
-- url     : https://prove2.me/theorems/792d7c6f-01fc-4f70-a92e-882fd18ce72a
-- title:
--   Global Theory: split Torus Points Equiv val
-- statement:
--   The Global Theory construction uses the split Torus Points Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L140-L144

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

theorem GlobalTheory.splitTorusPointsEquiv_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val := by sorry
