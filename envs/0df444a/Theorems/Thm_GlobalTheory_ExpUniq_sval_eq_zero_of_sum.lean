-- Prove2me | Theorems.Thm_GlobalTheory_ExpUniq_sval_eq_zero_of_sum
-- name    : GlobalTheory.ExpUniq.sval_eq_zero_of_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:49.945495+00:00
-- url     : https://prove2.me/theorems/920c72ea-864d-4e05-8eb3-72abc8aa0805
-- title:
--   Exp Uniq: sval eq zero of sum
-- statement:
--   The Exp Uniq construction uses the sval eq zero of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfWeightSum.lean#L63-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfWeightSum.lean#L63-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
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
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq

theorem GlobalTheory.ExpUniq.sval_eq_zero_of_sum {S B : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {L : LB B} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : X → K → (Y.left ⟶ B)) (ε : K → ℤ) (s : ∀ χ, LB.Sec (LB.LinComb L (φ χ) ε))
    (F : Finset X) (H : ∀ (w : (splitTorus S X ⊗ Y).left) J, Good L w J →
      ∑ χ ∈ F, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * sval (s χ) (snd (splitTorus S X) Y).left w J = 0)
    (α : X) (hα : α ∈ F) (y : Y.left) (J) (hJ : Good L y J) : sval (s α) (𝟙 _) y J = 0 := by sorry
