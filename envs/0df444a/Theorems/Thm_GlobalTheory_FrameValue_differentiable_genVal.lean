-- Prove2me | Theorems.Thm_GlobalTheory_FrameValue_differentiable_genVal
-- name    : GlobalTheory.FrameValue.differentiable_genVal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:49.305464+00:00
-- url     : https://prove2.me/theorems/831d052c-b8c7-428b-86b4-4a0c252d382d
-- title:
--   Frame Value: differentiable gen Val
-- statement:
--   The Frame Value construction uses the differentiable gen Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L185-L190

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}

theorem GlobalTheory.FrameValue.differentiable_genVal (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (p : A.left ⟶ Y) {q : E → Fin g → ℂ} (hq : Differentiable ℂ q)
    {z : E → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun w => z w k)
    (hz : ∀ w, IsLift u φ ((u.ex (q w)).left ≫ p) (z w)) :
    Differentiable ℂ fun w => genVal u hL t ((u.ex (q w)).left ≫ p) (z w) := by sorry
