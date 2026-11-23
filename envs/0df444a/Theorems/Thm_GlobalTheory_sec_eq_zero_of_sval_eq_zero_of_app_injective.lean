-- Prove2me | Theorems.Thm_GlobalTheory_sec_eq_zero_of_sval_eq_zero_of_app_injective
-- name    : GlobalTheory.sec_eq_zero_of_sval_eq_zero_of_app_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:23.935797+00:00
-- url     : https://prove2.me/theorems/c742f119-bc3c-40d4-be6b-15ebf2c941a9
-- title:
--   Global Theory: sec eq zero of sval eq zero of app injective
-- statement:
--   The Global Theory construction uses the sec eq zero of sval eq zero of app injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqZeroOfSvalWhiskerRightEqZero.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqZeroOfSvalWhiskerRightEqZero.lean#L16-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppWhiskerRightInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
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

theorem GlobalTheory.sec_eq_zero_of_sval_eq_zero_of_app_injective {X Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (hr : ∀ U : Y.Opens, Function.Injective (r.app U).hom) (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j : K → L.ι) : d.f j = 0 := by sorry
