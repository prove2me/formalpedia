-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_of_sval_eq_mul_unit
-- name    : GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:36.937292+00:00
-- url     : https://prove2.me/theorems/bee65dbb-9a34-44eb-8d7f-fe3e8b7e92c5
-- title:
--   Global Theory: exists ne zero of sval eq mul unit
-- statement:
--   The Global Theory construction uses the exists ne zero of sval eq mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsNeZeroIffSvalGenericPointNeZero.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsNeZeroIffSvalGenericPointNeZero.lean#L41-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsNeZeroIffSvalGenericPointNeZero
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
open GlobalTheory

theorem GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit : ∀ (Y X : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φ'' : K'' → (Y ⟶ X)) (ε'' : K'' → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (d : LB.Sec (LB.LinComb L φ'' ε'')), (∀ (y : Y) (J), Good L y J → ∃ v : (Y.presheaf.stalk y)ˣ, sval d (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J * v.val) → (∃ j, s.f j ≠ 0) → (∃ j, s'.f j ≠ 0) → ∃ j, d.f j ≠ 0 := by sorry
