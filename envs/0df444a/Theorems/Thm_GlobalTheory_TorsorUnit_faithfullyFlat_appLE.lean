-- Prove2me | Theorems.Thm_GlobalTheory_TorsorUnit_faithfullyFlat_appLE
-- name    : GlobalTheory.TorsorUnit.faithfullyFlat_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:40.969936+00:00
-- url     : https://prove2.me/theorems/50cf6391-0086-4969-b5ec-ea5aab956ee3
-- title:
--   Torsor Unit: faithfully Flat app LE
-- statement:
--   The Torsor Unit construction uses the faithfully Flat app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L364-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L364-L376

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
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
open GlobalTheory.TorsorUnit

theorem GlobalTheory.TorsorUnit.faithfullyFlat_appLE {Y B : Scheme.{0}} (q : Y ⟶ B) [Flat q] [Surjective q] {V : B.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (q ⁻¹ᵁ V)) :
    (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat := by sorry
