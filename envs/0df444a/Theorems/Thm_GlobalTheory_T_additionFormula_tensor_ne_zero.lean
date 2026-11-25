-- Prove2me | Theorems.Thm_GlobalTheory_T_additionFormula_tensor_ne_zero
-- name    : GlobalTheory.T.additionFormula_tensor_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:45:42.146463+00:00
-- url     : https://prove2.me/theorems/863c9526-eae5-4311-b515-4bcf2342b686
-- title:
--   T: addition Formula tensor ne zero
-- statement:
--   The T construction uses the addition Formula tensor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionFormulaTensorNeZeroStatement.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionFormulaTensorNeZeroStatement.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionFormulaTensorNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionFormulaTensorNeZeroStatement
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

theorem GlobalTheory.T.additionFormula_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by sorry
