-- Prove2me | Theorems.Thm_GlobalTheory_addB_tensor_ne_zero_iff
-- name    : GlobalTheory.addB_tensor_ne_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:30:25.852054+00:00
-- url     : https://prove2.me/theorems/85ffc6e1-e475-4894-b551-34511e70a2f0
-- title:
--   Global Theory: add B tensor ne zero iff
-- statement:
--   The Global Theory construction uses the add B tensor ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorAbelianPartNeZeroIff.lean#L53-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorAbelianPartNeZeroIff.lean#L53-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorAbelianPartNeZeroIff
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
open GlobalTheory.UU
open GlobalTheory

theorem GlobalTheory.addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by sorry
