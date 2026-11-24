-- Prove2me | Theorems.Thm_GlobalTheory_even_quadratic_pos_of_finite_nonpos
-- name    : GlobalTheory.even_quadratic_pos_of_finite_nonpos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:33.859375+00:00
-- url     : https://prove2.me/theorems/80601b7d-94ad-4a74-8070-a3fdbce455fb
-- title:
--   Global Theory: even quadratic pos of finite nonpos
-- statement:
--   The Global Theory construction uses the even quadratic pos of finite nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvenQuadraticPosOfFiniteNonpos.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvenQuadraticPosOfFiniteNonpos.lean#L38-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvenQuadraticPosOfFiniteNonpos
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

theorem GlobalTheory.even_quadratic_pos_of_finite_nonpos : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by sorry
