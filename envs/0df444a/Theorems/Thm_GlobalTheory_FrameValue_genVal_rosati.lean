-- Prove2me | Theorems.Thm_GlobalTheory_FrameValue_genVal_rosati
-- name    : GlobalTheory.FrameValue.genVal_rosati
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:18.277373+00:00
-- url     : https://prove2.me/theorems/dfde0a9d-985d-4e9f-8a7a-e986a9e38c72
-- title:
--   Frame Value: gen Val rosati
-- statement:
--   The Frame Value construction uses the gen Val rosati property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L439-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L439-L559

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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
variable [IsCommMonObj A] {f f' : A ⟶ A} {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

theorem GlobalTheory.FrameValue.genVal_rosati (hL : L.IsLB) (h : u.IsAH Hm χ) (hF : ∀ z, u.ex (F z) = u.ex z ≫ f)
    (hG : ∀ z, u.ex (G z) = u.ex z ≫ f') (r : LB.Gen (LB.LinComb L (Out.rosatiφ A f f') Out.rosatiε)) (hr : r.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r (Out.zero2 A)) (LB.oneGen L)) :
    (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
      ∀ x z, genVal u hL r (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) = 1 := by sorry
