-- Prove2me | Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_of_range_subset
-- name    : GlobalTheory.exists_specMap_fromSpec_of_range_subset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:56.363246+00:00
-- url     : https://prove2.me/theorems/ab1a1298-c632-436b-9326-3a3e853ce639
-- title:
--   Global Theory: exists spec Map from Spec of range subset
-- statement:
--   The Global Theory construction uses the exists spec Map from Spec of range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSpecMapFromSpecOfRangeSubset.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSpecMapFromSpecOfRangeSubset.lean#L14-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSpecMapFromSpecOfRangeSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_specMap_fromSpec_of_range_subset {A : CommRingCat.{0}} {X : Scheme.{0}} (f : Spec A ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : ∀ x, f x ∈ U) :
    ∃ φ : Γ(X, U) ⟶ A, Spec.map φ ≫ hU.fromSpec = f := by sorry
