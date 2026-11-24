-- Prove2me | Theorems.Thm_GlobalTheory_WeightVal_eq_zero_of_stalk_sum
-- name    : GlobalTheory.WeightVal.eq_zero_of_stalk_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:16.602806+00:00
-- url     : https://prove2.me/theorems/3aeb25a0-59ee-4cf7-a843-8a4a112388fb
-- title:
--   Weight Val: eq zero of stalk sum
-- statement:
--   The Weight Val construction uses the eq zero of stalk sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfSumMulCoord.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfSumMulCoord.lean#L23-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.WeightVal

theorem GlobalTheory.WeightVal.eq_zero_of_stalk_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens}
    (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by sorry
