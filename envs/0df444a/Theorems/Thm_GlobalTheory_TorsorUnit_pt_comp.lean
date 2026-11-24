-- Prove2me | Theorems.Thm_GlobalTheory_TorsorUnit_pt_comp
-- name    : GlobalTheory.TorsorUnit.pt_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:45.563552+00:00
-- url     : https://prove2.me/theorems/16a94e2a-b162-4516-8f45-cdb9d4693495
-- title:
--   Torsor Unit: pt comp
-- statement:
--   The Torsor Unit construction uses the pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L208-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L208-L213

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}

theorem GlobalTheory.TorsorUnit.pt_comp {B : Scheme.{0}} {V : B.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : Y ⟶ B) (e : U ≤ q ⁻¹ᵁ V) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    pt hU θ ≫ q = pt hV (θ.comp (q.appLE V U e).hom) := by sorry
