-- Prove2me | Theorems.Thm_GlobalTheory_exists_splitExt_isGt_of_torusExtension
-- name    : GlobalTheory.exists_splitExt_isGt_of_torusExtension
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:44.730431+00:00
-- url     : https://prove2.me/theorems/e7e58014-57b5-4d3e-85c1-e7a713a133c4
-- title:
--   Global Theory: exists split Ext is Gt of torus Extension
-- statement:
--   The Global Theory construction uses the exists split Ext is Gt of torus Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtIsGtOfTorusExtension.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtIsGtOfTorusExtension.lean#L14-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_splitExt_isGt_of_torusExtension :
    ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → ∃ E : SplitExt (Spec (CommRingCat.of K)), E.IsGt G := by sorry
