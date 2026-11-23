-- Prove2me | Theorems.Thm_GlobalTheory_UnifLieBasis_snd_evalPt_mul
-- name    : GlobalTheory.UnifLieBasis.snd_evalPt_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:31.778812+00:00
-- url     : https://prove2.me/theorems/13d98375-e394-490d-8d51-c265c5b2cfb9
-- title:
--   Unif Lie Basis: snd eval Pt mul
-- statement:
--   The Unif Lie Basis construction uses the snd eval Pt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLieBasisOfHolUnif.lean#L38-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLieBasisOfHolUnif.lean#L38-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
omit u

theorem GlobalTheory.UnifLieBasis.snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by sorry
