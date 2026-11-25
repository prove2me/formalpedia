-- Prove2me | Theorems.Thm_GlobalTheory_UnifZero_unit_pow_mul_app
-- name    : GlobalTheory.UnifZero.unit_pow_mul_app
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:41.643742+00:00
-- url     : https://prove2.me/theorems/392d4a93-14f6-46c3-82f3-e96e0b712821
-- title:
--   Unif Zero: unit pow mul app
-- statement:
--   The Unif Zero construction uses the unit pow mul app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L82-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']

theorem GlobalTheory.UnifZero.unit_pow_mul_app (f : Y' ⟶ Y) {U : Y.Opens} {V W : Y'.Opens} (h : W ≤ V) (h' : W ≤ f ⁻¹ᵁ U)
    {u : Γ(Y', V)ˣ} (hu : u = 1) {x : Γ(Y, U)} {a : Γ(Y, ⊤)} (hx : x = resTop U a) (k : ℕ) :
    (res h u).val ^ k * (Y'.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) =
      resTop W (f.appTop.hom a) := by sorry
