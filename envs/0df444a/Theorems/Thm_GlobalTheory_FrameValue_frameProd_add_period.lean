-- Prove2me | Theorems.Thm_GlobalTheory_FrameValue_frameProd_add_period
-- name    : GlobalTheory.FrameValue.frameProd_add_period
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:15.924344+00:00
-- url     : https://prove2.me/theorems/8cc7d998-ecd4-4c7a-886d-67ea98266155
-- title:
--   Frame Value: frame Prod add period
-- statement:
--   The Frame Value construction uses the frame Prod add period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L202-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L202-L208

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
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem GlobalTheory.FrameValue.frameProd_add_period (h : u.IsAH Hm χ) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (ε : K → ℤ)
    (l : K → u.Λ) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    frameProd u ε z j = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * frameProd u ε (fun k => z k + l k) j := by sorry
